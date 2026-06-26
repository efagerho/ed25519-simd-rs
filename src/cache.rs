use crate::batch::{
    DecompressedRBatch8, PreparedVerificationBatch8WithoutR, VerifyInput, VerifyPolicy,
    decode_and_build_tables8_wide, decode_keys_and_decompress_r8_wide,
    decompress_r_batch_wide_simd, r_encoding_has_canonical_y, r_encoding_is_legacy_excluded,
    verify_prepared_batch8_dalek_projective_simd, verify_prepared_batch8_dalek_simd,
    verify_prepared_batch8_zip215_simd,
};
use crate::edwards::{BasepointTable, EdwardsPoint, PointTable};
use crate::scalar::{self, Radix16, Scalar};
use crate::sha512;
use std::collections::HashMap;

const SIMD_LANES: usize = crate::batch::SIMD_LANES;
// TODO: Consider sparse bucketing for longer messages instead of falling back
// to comparison sorting.
const BUCKET_HISTOGRAM_BLOCKS: usize = 64;

#[cold]
#[inline(never)]
fn assert_required_avx512_runtime_support() {
    if let Err(reason) = required_avx512_runtime_support() {
        panic!(
            "ed25519-simd was built for AVX-512 (F, DQ, IFMA) but cannot run \
             safely on this host: {reason}; build and run on an AVX-512 IFMA \
             capable CPU with OS AVX-512 state support enabled"
        );
    }
}

#[inline(never)]
fn required_avx512_runtime_support() -> Result<(), &'static str> {
    use std::arch::x86_64::{__cpuid, __cpuid_count, _xgetbv};

    const CPUID_1_ECX_XSAVE: u32 = 1 << 26;
    const CPUID_1_ECX_OSXSAVE: u32 = 1 << 27;
    const CPUID_1_ECX_AVX: u32 = 1 << 28;
    const CPUID_7_EBX_AVX512F: u32 = 1 << 16;
    const CPUID_7_EBX_AVX512DQ: u32 = 1 << 17;
    const CPUID_7_EBX_AVX512IFMA: u32 = 1 << 21;
    const XCR0_AVX512_STATE: u64 = (1 << 0) | (1 << 1) | (1 << 2) | (1 << 5) | (1 << 6) | (1 << 7);

    unsafe {
        let max_leaf = __cpuid(0).eax;
        if max_leaf < 7 {
            return Err("CPUID leaf 7 is unavailable");
        }

        let leaf1 = __cpuid(1);
        if leaf1.ecx & CPUID_1_ECX_XSAVE == 0 {
            return Err("CPU does not support XSAVE/XGETBV");
        }
        if leaf1.ecx & CPUID_1_ECX_OSXSAVE == 0 {
            return Err("OS has not enabled XSAVE/XGETBV");
        }
        if leaf1.ecx & CPUID_1_ECX_AVX == 0 {
            return Err("CPU does not support AVX");
        }

        let xcr0 = _xgetbv(0);
        if xcr0 & XCR0_AVX512_STATE != XCR0_AVX512_STATE {
            return Err("OS has not enabled AVX-512 register state");
        }

        let leaf7 = __cpuid_count(7, 0);
        if leaf7.ebx & CPUID_7_EBX_AVX512F == 0 {
            return Err("CPU does not support AVX-512F");
        }
        if leaf7.ebx & CPUID_7_EBX_AVX512DQ == 0 {
            return Err("CPU does not support AVX-512DQ");
        }
        if leaf7.ebx & CPUID_7_EBX_AVX512IFMA == 0 {
            return Err("CPU does not support AVX-512IFMA");
        }
    }

    Ok(())
}

/// A decoded public key and its precomputed multiplication table.
#[derive(Clone, Debug)]
pub struct CachedPublicKey {
    pub encoded: [u8; 32],
    table: PointTable,
}

impl CachedPublicKey {
    /// Decode and precompute a public key table.
    pub fn decode(encoded: [u8; 32]) -> Option<Self> {
        EdwardsPoint::decompress(&encoded).map(|point| Self {
            encoded,
            table: PointTable::new(&point),
        })
    }

    pub(crate) fn table(&self) -> &PointTable {
        &self.table
    }

    /// Wrap an already-built table (e.g. from a fused 8-wide decode).
    pub(crate) fn from_table(encoded: [u8; 32], table: PointTable) -> Self {
        Self { encoded, table }
    }

    /// Decode eight keys 8-wide and return a per-lane validity mask.
    pub(crate) fn decode_batch8(encoded: &[[u8; 32]; SIMD_LANES]) -> ([Self; SIMD_LANES], u8) {
        let (tables, valid_mask) = decode_and_build_tables8_wide(encoded);
        let mut tables = tables.into_iter();
        let keys = core::array::from_fn(|i| Self {
            encoded: encoded[i],
            table: tables.next().unwrap(),
        });
        (keys, valid_mask)
    }
}

/// Storage policy for decoded public keys.
///
/// The default [`LruKeyCache`] retains keys across batches. [`NullKeyCache`]
/// retains no decoded keys and is meant for cold workloads where keys do not
/// repeat.
pub trait KeyCache {
    /// Try to make the key available through [`get`](Self::get).
    fn prepare(&mut self, encoded: [u8; 32]) -> bool;

    /// Borrow a key prepared earlier in the same batch, or `None` if it is
    /// absent or invalid.
    fn get(&self, encoded: &[u8; 32]) -> Option<&CachedPublicKey>;

    /// Try to make eight keys available through [`get`](Self::get).
    fn prepare_batch8(&mut self, keys: &[[u8; 32]; 8]) -> bool {
        let mut ok = true;
        for key in keys {
            ok &= self.prepare(*key);
        }
        ok
    }

    /// Optionally retain an already-decoded key for later chunks or batches.
    fn store(&mut self, key: CachedPublicKey) {
        self.prepare(key.encoded);
    }

    /// Called by [`Verifier::verify_batch`] after each batch completes.
    fn end_batch(&mut self) {}
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CacheStats {
    pub keys: usize,
    pub pinned_keys: usize,
    pub max_keys: Option<usize>,
    pub hits: u64,
    pub misses: u64,
    pub inserts: u64,
    pub evictions: u64,
}

#[derive(Clone, Debug)]
struct LruEntry {
    key: CachedPublicKey,
    hits: u64,
    last_used: u64,
    pinned: bool,
}

/// The default [`KeyCache`]: keeps decoded keys in a map across batches, with
/// optional capacity and least-valuable eviction. Best for workloads with a hot
/// set of repeating keys.
#[derive(Debug)]
pub struct LruKeyCache {
    keys: HashMap<[u8; 32], LruEntry>,
    max_cached_keys: Option<usize>,
    hits: u64,
    misses: u64,
    inserts: u64,
    evictions: u64,
    clock: u64,
}

impl Default for LruKeyCache {
    fn default() -> Self {
        Self::new()
    }
}

impl LruKeyCache {
    pub fn new() -> Self {
        Self {
            keys: HashMap::new(),
            max_cached_keys: None,
            hits: 0,
            misses: 0,
            inserts: 0,
            evictions: 0,
            clock: 0,
        }
    }

    pub fn with_capacity(max_cached_keys: usize) -> Self {
        let mut cache = Self::new();
        cache.set_capacity(Some(max_cached_keys));
        cache
    }

    pub fn set_capacity(&mut self, max_cached_keys: Option<usize>) {
        self.max_cached_keys = max_cached_keys.map(|keys| keys.max(1));
        self.evict_to_capacity(None);
    }

    pub fn stats(&self) -> CacheStats {
        CacheStats {
            keys: self.keys.len(),
            pinned_keys: self.keys.values().filter(|entry| entry.pinned).count(),
            max_keys: self.max_cached_keys,
            hits: self.hits,
            misses: self.misses,
            inserts: self.inserts,
            evictions: self.evictions,
        }
    }

    pub fn hot_public_keys(&self, limit: usize) -> Vec<[u8; 32]> {
        let mut entries: Vec<&LruEntry> = self.keys.values().collect();
        entries.sort_by(|lhs, rhs| {
            rhs.hits
                .cmp(&lhs.hits)
                .then_with(|| rhs.last_used.cmp(&lhs.last_used))
        });
        entries
            .into_iter()
            .take(limit)
            .map(|entry| entry.key.encoded)
            .collect()
    }

    /// Decode and pin the given keys so they are not evicted.
    pub fn preload(&mut self, keys: &[[u8; 32]]) {
        for key in keys {
            self.touch_or_insert(*key, true);
        }
    }

    fn touch_or_insert(&mut self, encoded: [u8; 32], pinned: bool) -> bool {
        self.clock = self.clock.wrapping_add(1);
        let last_used = self.clock;

        if let Some(entry) = self.keys.get_mut(&encoded) {
            self.hits = self.hits.wrapping_add(1);
            entry.hits = entry.hits.wrapping_add(1);
            entry.last_used = last_used;
            entry.pinned |= pinned;
            return true;
        }

        self.insert(encoded, pinned, last_used)
    }

    fn insert_cached(&mut self, key: CachedPublicKey, pinned: bool, last_used: u64) {
        let encoded = key.encoded;
        self.keys.insert(
            encoded,
            LruEntry {
                key,
                hits: 1,
                last_used,
                pinned,
            },
        );
        self.inserts = self.inserts.wrapping_add(1);
    }

    #[cold]
    #[inline(never)]
    fn insert(&mut self, encoded: [u8; 32], pinned: bool, last_used: u64) -> bool {
        self.misses = self.misses.wrapping_add(1);
        let Some(key) = CachedPublicKey::decode(encoded) else {
            return false;
        };
        self.insert_cached(key, pinned, last_used);
        self.evict_to_capacity(Some(encoded));
        true
    }

    fn evict_to_capacity(&mut self, protected: Option<[u8; 32]>) {
        let Some(max_cached_keys) = self.max_cached_keys else {
            return;
        };

        while self.keys.len() > max_cached_keys {
            let victim = self
                .keys
                .iter()
                .filter(|(encoded, entry)| Some(**encoded) != protected && !entry.pinned)
                .min_by_key(|(_, entry)| (entry.hits, entry.last_used))
                .map(|(encoded, _)| *encoded);

            let Some(victim) = victim else {
                break;
            };
            self.keys.remove(&victim);
            self.evictions = self.evictions.wrapping_add(1);
        }
    }
}

impl KeyCache for LruKeyCache {
    #[inline]
    fn prepare(&mut self, encoded: [u8; 32]) -> bool {
        self.touch_or_insert(encoded, false)
    }

    fn prepare_batch8(&mut self, keys: &[[u8; 32]; 8]) -> bool {
        // Cache hits are served here; only the misses are decoded 8-wide below.
        // `missing` is sized for all eight lanes but the hit lanes keep their
        // zero-filled placeholder: `decode_batch8` always decodes all eight, but
        // the second loop processes a lane only if its `missing_mask` bit is set,
        // so the throwaway placeholder tables for hit lanes are simply discarded.
        let mut missing = [[0u8; 32]; 8];
        let mut missing_mask = 0u8;
        let mut last_used = [0u64; 8];
        let mut lane = 0;
        while lane < 8 {
            self.clock = self.clock.wrapping_add(1);
            last_used[lane] = self.clock;
            if let Some(entry) = self.keys.get_mut(&keys[lane]) {
                self.hits = self.hits.wrapping_add(1);
                entry.hits = entry.hits.wrapping_add(1);
                entry.last_used = last_used[lane];
            } else {
                missing[lane] = keys[lane];
                missing_mask |= 1 << lane;
            }
            lane += 1;
        }

        if missing_mask == 0 {
            return true;
        }

        let (decoded, valid_mask) = CachedPublicKey::decode_batch8(&missing);
        let mut ok = true;
        for (lane, key) in decoded.into_iter().enumerate() {
            if missing_mask & (1 << lane) == 0 {
                continue;
            }

            if let Some(entry) = self.keys.get_mut(&keys[lane]) {
                self.hits = self.hits.wrapping_add(1);
                entry.hits = entry.hits.wrapping_add(1);
                entry.last_used = last_used[lane];
            } else {
                self.misses = self.misses.wrapping_add(1);
                if valid_mask & (1 << lane) != 0 {
                    self.insert_cached(key, false, last_used[lane]);
                } else {
                    ok = false;
                }
            }
        }
        ok
    }

    fn store(&mut self, key: CachedPublicKey) {
        self.clock = self.clock.wrapping_add(1);
        let last_used = self.clock;
        if let Some(entry) = self.keys.get_mut(&key.encoded) {
            entry.hits = entry.hits.wrapping_add(1);
            entry.last_used = last_used;
        } else {
            self.misses = self.misses.wrapping_add(1);
            self.insert_cached(key, false, last_used);
        }
    }

    #[inline]
    fn end_batch(&mut self) {
        self.evict_to_capacity(None);
    }

    #[inline]
    fn get(&self, encoded: &[u8; 32]) -> Option<&CachedPublicKey> {
        self.keys.get(encoded).map(|entry| &entry.key)
    }
}

/// A [`KeyCache`] that retains no decoded keys.
#[derive(Clone, Copy, Debug, Default)]
pub struct NullKeyCache;

impl NullKeyCache {
    pub fn new() -> Self {
        Self
    }
}

impl KeyCache for NullKeyCache {
    #[inline]
    fn prepare(&mut self, _encoded: [u8; 32]) -> bool {
        false
    }

    #[inline]
    fn get(&self, _encoded: &[u8; 32]) -> Option<&CachedPublicKey> {
        None
    }

    #[inline]
    fn prepare_batch8(&mut self, _keys: &[[u8; 32]; 8]) -> bool {
        false
    }

    #[inline]
    fn store(&mut self, _key: CachedPublicKey) {}
}

#[derive(Debug)]
pub struct Verifier<C: KeyCache = LruKeyCache> {
    policy: VerifyPolicy,
    base_table: BasepointTable,
    identity_table: PointTable,
    bucket_order: Vec<usize>,
    cache: C,
}

impl Default for Verifier<LruKeyCache> {
    fn default() -> Self {
        Self::new()
    }
}

impl Verifier<LruKeyCache> {
    pub fn new() -> Self {
        Self::with_policy(VerifyPolicy::default())
    }

    pub fn with_policy(policy: VerifyPolicy) -> Self {
        Self::with_cache(policy, LruKeyCache::new())
    }

    pub fn with_policy_and_cache_capacity(policy: VerifyPolicy, max_cached_keys: usize) -> Self {
        Self::with_cache(policy, LruKeyCache::with_capacity(max_cached_keys))
    }

    pub fn set_cache_capacity(&mut self, max_cached_keys: Option<usize>) {
        self.cache.set_capacity(max_cached_keys);
    }

    pub fn preload_public_keys(&mut self, keys: &[[u8; 32]]) {
        self.cache.preload(keys);
    }
}

impl<C: KeyCache> Verifier<C> {
    pub fn with_cache(policy: VerifyPolicy, cache: C) -> Self {
        assert_required_avx512_runtime_support();
        Self {
            policy,
            base_table: BasepointTable::new(),
            identity_table: PointTable::new(&EdwardsPoint::identity()),
            bucket_order: Vec::new(),
            cache,
        }
    }

    pub fn cache(&self) -> &C {
        &self.cache
    }

    pub fn cache_mut(&mut self) -> &mut C {
        &mut self.cache
    }

    pub fn policy(&self) -> VerifyPolicy {
        self.policy
    }

    #[cfg(test)]
    pub(crate) fn verify_one(&mut self, input: VerifyInput<'_>) -> bool {
        let padded: [VerifyInput<'_>; SIMD_LANES] = [input; SIMD_LANES];
        let mut out = [false; SIMD_LANES];
        self.try_verify_chunk(&padded, &mut out);
        out[0]
    }

    pub fn verify_batch(&mut self, inputs: &[VerifyInput<'_>], out: &mut [bool]) {
        assert_eq!(inputs.len(), out.len());
        if should_bucket_by_block_count(inputs) {
            self.verify_batch_block_bucketed(inputs, out);
        } else {
            self.verify_batch_in_order(inputs, out);
        }

        self.cache.end_batch();
    }

    fn verify_batch_in_order(&mut self, inputs: &[VerifyInput<'_>], out: &mut [bool]) {
        let mut i = 0;
        while i + SIMD_LANES <= inputs.len() {
            self.try_verify_chunk(&inputs[i..i + SIMD_LANES], &mut out[i..i + SIMD_LANES]);
            i += SIMD_LANES;
        }

        let rem = inputs.len() - i;
        if rem > 0 {
            let mut padded: [VerifyInput<'_>; SIMD_LANES] = [inputs[inputs.len() - 1]; SIMD_LANES];
            padded[..rem].copy_from_slice(&inputs[i..]);
            let mut tmp = [false; SIMD_LANES];
            self.try_verify_chunk(&padded, &mut tmp);
            out[i..].copy_from_slice(&tmp[..rem]);
        }
    }

    fn verify_batch_block_bucketed(&mut self, inputs: &[VerifyInput<'_>], out: &mut [bool]) {
        build_block_bucket_order(inputs, &mut self.bucket_order);

        let mut i = 0;
        while i + SIMD_LANES <= self.bucket_order.len() {
            let mut chunk = [inputs[self.bucket_order[i]]; SIMD_LANES];
            let mut lane = 0;
            while lane < SIMD_LANES {
                chunk[lane] = inputs[self.bucket_order[i + lane]];
                lane += 1;
            }

            let mut tmp = [false; SIMD_LANES];
            self.try_verify_chunk(&chunk, &mut tmp);

            lane = 0;
            while lane < SIMD_LANES {
                out[self.bucket_order[i + lane]] = tmp[lane];
                lane += 1;
            }
            i += SIMD_LANES;
        }

        let rem = self.bucket_order.len() - i;
        if rem > 0 {
            let last = self.bucket_order[self.bucket_order.len() - 1];
            let mut chunk = [inputs[last]; SIMD_LANES];
            let mut lane = 0;
            while lane < rem {
                chunk[lane] = inputs[self.bucket_order[i + lane]];
                lane += 1;
            }

            let mut tmp = [false; SIMD_LANES];
            self.try_verify_chunk(&chunk, &mut tmp);

            lane = 0;
            while lane < rem {
                out[self.bucket_order[i + lane]] = tmp[lane];
                lane += 1;
            }
        }
    }

    fn try_verify_chunk(&mut self, inputs: &[VerifyInput<'_>], out: &mut [bool]) {
        debug_assert_eq!(inputs.len(), SIMD_LANES);
        debug_assert_eq!(out.len(), SIMD_LANES);
        let policy = self.policy;

        let first_public_key = inputs[0].public_key;
        let uniform_public_key = inputs[1..]
            .iter()
            .all(|input| input.public_key == first_public_key);

        // Parse R, public keys, and s (per-lane validity for non-canonical s).
        let mut valid = [true; SIMD_LANES];
        let mut r_bytes = [[0u8; 32]; SIMD_LANES];
        let mut public_keys = [[0u8; 32]; SIMD_LANES];
        let mut s_digits = [[0i8; 65]; SIMD_LANES];
        let mut lane = 0;
        while lane < SIMD_LANES {
            r_bytes[lane].copy_from_slice(&inputs[lane].signature[..32]);

            let mut s_bytes = [0u8; 32];
            s_bytes.copy_from_slice(&inputs[lane].signature[32..]);
            if scalar::is_canonical(&s_bytes) {
                s_digits[lane] = Scalar::from_canonical_bytes(s_bytes).to_radix16();
            } else {
                valid[lane] = false;
            }
            public_keys[lane] = inputs[lane].public_key;
            lane += 1;
        }

        let mut decoded_r: Option<(DecompressedRBatch8, u8)> = None;
        let mut uniform_decoded_key: Option<CachedPublicKey> = None;
        let mut decoded_keys: Option<([CachedPublicKey; SIMD_LANES], u8)> = None;
        if uniform_public_key {
            if !self.cache.prepare(first_public_key) {
                uniform_decoded_key = CachedPublicKey::decode(first_public_key);
            }
        } else if !public_keys.iter().all(|key| self.cache.get(key).is_some()) {
            let (tables, key_mask, r_points, r_mask) =
                decode_keys_and_decompress_r8_wide(&public_keys, &r_bytes);
            let mut tables = tables.into_iter();
            decoded_keys = Some((
                core::array::from_fn(|lane| {
                    CachedPublicKey::from_table(public_keys[lane], tables.next().unwrap())
                }),
                key_mask,
            ));
            decoded_r = Some((r_points, r_mask));
        } else {
            self.cache.prepare_batch8(&public_keys);
        }

        let mut messages = [inputs[0].message; SIMD_LANES];
        lane = 1;
        while lane < SIMD_LANES {
            messages[lane] = inputs[lane].message;
            lane += 1;
        }
        let digests = sha512::hash_ed25519_challenges8(&r_bytes, &public_keys, messages);

        let mut k_digits: [Radix16; SIMD_LANES] = [[0i8; 65]; SIMD_LANES];
        lane = 0;
        while lane < SIMD_LANES {
            k_digits[lane] = Scalar::from_wide_bytes(digests[lane]).to_radix16();
            lane += 1;
        }

        {
            let mut public_key_tables: [&PointTable; SIMD_LANES] =
                [&self.identity_table; SIMD_LANES];
            lane = 0;
            while lane < SIMD_LANES {
                if let Some(key) = self.cache.get(&public_keys[lane]) {
                    public_key_tables[lane] = key.table();
                } else if let Some(key) = &uniform_decoded_key {
                    if key.encoded == public_keys[lane] {
                        public_key_tables[lane] = key.table();
                    } else {
                        valid[lane] = false;
                    }
                } else if let Some((keys, key_mask)) = &decoded_keys {
                    if key_mask & (1 << lane) != 0 {
                        public_key_tables[lane] = keys[lane].table();
                    } else {
                        valid[lane] = false;
                    }
                } else {
                    valid[lane] = false;
                }
                lane += 1;
            }

            let prepared = PreparedVerificationBatch8WithoutR {
                public_key_tables,
                s_digits,
                k_digits,
            };
            let out: &mut [bool; SIMD_LANES] = out.try_into().expect("exact SIMD chunk");

            match policy {
                VerifyPolicy::Zip215 => {
                    let (r_points, r_mask) = match decoded_r {
                        Some(decoded) => decoded,
                        None => decompress_r_batch_wide_simd(&r_bytes),
                    };
                    let simd =
                        verify_prepared_batch8_zip215_simd(&prepared, &r_points, &self.base_table);
                    lane = 0;
                    while lane < SIMD_LANES {
                        out[lane] = simd[lane] && valid[lane] && (r_mask & (1 << lane) != 0);
                        lane += 1;
                    }
                }
                VerifyPolicy::Dalek => {
                    if let Some((r_points, r_mask)) = decoded_r {
                        let simd = verify_prepared_batch8_dalek_projective_simd(
                            &prepared,
                            &r_points,
                            &self.base_table,
                        );
                        lane = 0;
                        while lane < SIMD_LANES {
                            let legacy_excluded = public_keys[lane] == [0u8; 32]
                                || r_encoding_is_legacy_excluded(&r_bytes[lane]);
                            out[lane] = simd[lane]
                                && valid[lane]
                                && (r_mask & (1 << lane) != 0)
                                && r_encoding_has_canonical_y(&r_bytes[lane])
                                && !legacy_excluded;
                            lane += 1;
                        }
                    } else {
                        let simd = verify_prepared_batch8_dalek_simd(
                            &prepared,
                            &r_bytes,
                            &self.base_table,
                        );
                        lane = 0;
                        while lane < SIMD_LANES {
                            let legacy_excluded = public_keys[lane] == [0u8; 32]
                                || r_encoding_is_legacy_excluded(&r_bytes[lane]);
                            out[lane] = simd[lane] && valid[lane] && !legacy_excluded;
                            lane += 1;
                        }
                    }
                }
            }
        }

        if let Some(key) = uniform_decoded_key {
            self.cache.store(key);
        }
        if let Some((keys, key_mask)) = decoded_keys {
            for (lane, key) in keys.into_iter().enumerate() {
                if key_mask & (1 << lane) != 0 {
                    self.cache.store(key);
                }
            }
        }
    }
}

fn should_bucket_by_block_count(inputs: &[VerifyInput<'_>]) -> bool {
    if inputs.len() < SIMD_LANES * 2 {
        return false;
    }

    let first = challenge_block_count(inputs[0].message.len());
    let mut i = 1;
    while i < inputs.len() {
        if challenge_block_count(inputs[i].message.len()) != first {
            return true;
        }
        i += 1;
    }
    false
}

fn build_block_bucket_order(inputs: &[VerifyInput<'_>], order: &mut Vec<usize>) {
    let mut max_block_count = 0usize;
    let mut i = 0;
    while i < inputs.len() {
        max_block_count = max_block_count.max(challenge_block_count(inputs[i].message.len()));
        i += 1;
    }

    order.clear();
    if max_block_count > BUCKET_HISTOGRAM_BLOCKS {
        order.extend(0..inputs.len());
        order.sort_unstable_by_key(|&idx| challenge_block_count(inputs[idx].message.len()));
        return;
    }

    let mut counts = [0usize; BUCKET_HISTOGRAM_BLOCKS + 1];
    i = 0;
    while i < inputs.len() {
        counts[challenge_block_count(inputs[i].message.len())] += 1;
        i += 1;
    }

    let mut next = [0usize; BUCKET_HISTOGRAM_BLOCKS + 1];
    let mut total = 0usize;
    i = 0;
    while i < counts.len() {
        next[i] = total;
        total += counts[i];
        i += 1;
    }

    order.resize(inputs.len(), 0);
    i = 0;
    while i < inputs.len() {
        let block_count = challenge_block_count(inputs[i].message.len());
        let pos = next[block_count];
        next[block_count] += 1;
        order[pos] = i;
        i += 1;
    }
}

#[inline]
fn challenge_block_count(message_len: usize) -> usize {
    (64 + message_len + 1 + 16).div_ceil(128)
}
