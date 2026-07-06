use crate::batch::{self, PreparedBatch};
use crate::cache::{CachedPublicKey, KeyCache, NullKeyCache};
use crate::cpuid;
use crate::edwards::{BasepointTable, EdwardsPoint, PointTable};
use crate::lru_cache::LruKeyCache;
use crate::policy::{VerifyPolicy, r_encoding_is_legacy_excluded};
use crate::scalar::{self, Radix16, Scalar};
use crate::sha512;
use crate::wide::avx512ifma;
use std::sync::LazyLock;

#[derive(Clone, Copy, Debug)]
pub struct VerifyInput<'a> {
    pub public_key: [u8; batch::PUBLIC_KEY_LEN],
    pub signature: [u8; batch::SIGNATURE_LEN],
    pub message: &'a [u8],
}

const SIMD_LANES: usize = batch::SIMD_LANES;

// The base-point table (all 273 precomputed multiples used by the multi-scalar
// ladder, ~43KB) is identical for every `Verifier` regardless of policy or
// cache choice, so it's built once per process and shared by reference rather
// than reconstructed (135 point doublings/additions) for every instance.
static BASE_TABLE: LazyLock<BasepointTable> = LazyLock::new(BasepointTable::new);

#[derive(Debug)]
pub struct Verifier<C: KeyCache = NullKeyCache> {
    policy: VerifyPolicy,
    base_table: &'static BasepointTable,
    identity_table: PointTable,
    bucket_order: Vec<usize>,
    cache: C,
}

impl Default for Verifier<NullKeyCache> {
    fn default() -> Self {
        Self::new()
    }
}

impl Verifier<NullKeyCache> {
    /// Create a verifier with the default policy and no retained-key cache.
    pub fn new() -> Self {
        Self::with_policy(VerifyPolicy::default())
    }

    /// Create a verifier with a specific policy and no retained-key cache.
    pub fn with_policy(policy: VerifyPolicy) -> Self {
        Self::with_cache(policy, NullKeyCache::new())
    }
}

impl Verifier<LruKeyCache> {
    /// Create a verifier with a specific policy and capacity-bounded evictable LRU cache.
    pub fn with_cache_capacity(policy: VerifyPolicy, max_cached_keys: usize) -> Self {
        Self::with_cache(policy, LruKeyCache::with_capacity(max_cached_keys))
    }

    /// Decode and pin keys in the LRU cache outside the eviction bound.
    pub fn preload_public_keys(&mut self, keys: &[[u8; 32]]) {
        self.cache.preload(keys);
    }
}

impl<C: KeyCache> Verifier<C> {
    /// Create a verifier backed by a caller-provided cache.
    pub fn with_cache(policy: VerifyPolicy, cache: C) -> Self {
        cpuid::assert_required_avx512_runtime_support();
        Self {
            policy,
            base_table: &*BASE_TABLE,
            identity_table: PointTable::new(&EdwardsPoint::identity()),
            bucket_order: Vec::new(),
            cache,
        }
    }

    /// Borrow the configured cache.
    pub fn cache(&self) -> &C {
        &self.cache
    }

    /// Mutably borrow the configured cache.
    pub fn cache_mut(&mut self) -> &mut C {
        &mut self.cache
    }

    /// Return the verifier policy.
    pub fn policy(&self) -> VerifyPolicy {
        self.policy
    }

    /// Verify a batch and write one boolean result per input.
    pub fn verify_batch(&mut self, inputs: &[VerifyInput<'_>], out: &mut [bool]) {
        assert_eq!(inputs.len(), out.len());
        let mut bucket_order = core::mem::take(&mut self.bucket_order);
        batch::for_each_simd_chunk(inputs, &mut bucket_order, |chunk, output_indices, lanes| {
            let mut tmp = [false; SIMD_LANES];
            self.try_verify_chunk(chunk, &mut tmp);

            let mut lane = 0;
            while lane < lanes {
                out[output_indices[lane]] = tmp[lane];
                lane += 1;
            }
        });
        self.bucket_order = bucket_order;
    }

    fn try_verify_chunk(
        &mut self,
        inputs: &[VerifyInput<'_>; SIMD_LANES],
        out: &mut [bool; SIMD_LANES],
    ) {
        let policy = self.policy;

        let first_public_key = inputs[0].public_key;
        let uniform_public_key = inputs[1..]
            .iter()
            .all(|input| input.public_key == first_public_key);

        // Parse R, public keys, and s (per-lane validity for non-canonical s).
        let mut valid = [true; SIMD_LANES];
        let mut r_bytes = [[0u8; 32]; SIMD_LANES];
        let mut public_keys = [[0u8; 32]; SIMD_LANES];
        let mut s_digits = [[0i8; 64]; SIMD_LANES];
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

        let mut decoded_r: Option<(avx512ifma::WideRPoints, [bool; SIMD_LANES])> = None;
        let mut uniform_cached_key: Option<&CachedPublicKey> = None;
        let mut uniform_decoded_key: Option<CachedPublicKey> = None;
        let mut cached_keys: Option<[Option<&CachedPublicKey>; SIMD_LANES]> = None;
        let mut decoded_keys: Option<([CachedPublicKey; SIMD_LANES], [bool; SIMD_LANES])> = None;
        let mut missing_key_lanes = [false; SIMD_LANES];
        if uniform_public_key {
            uniform_cached_key = self.cache.get(&first_public_key);
            if uniform_cached_key.is_none() {
                missing_key_lanes = [true; SIMD_LANES];
                // Decode the (duplicated) key and R together through the same
                // interleaved SIMD path the non-uniform miss branch below
                // uses, instead of a solo scalar key decode followed by a
                // separate solo R decompression: the two inverse-square-root
                // chains share the same IFMA latency, so fusing them is
                // strictly cheaper than running either alone. Redundant SIMD
                // lanes on identical input are free, so only lane 0 is kept.
                let uniform_keys = [first_public_key; SIMD_LANES];
                let (tables, key_valid_bits, r_points, r_valid_bits) =
                    avx512ifma::decode_keys_and_decompress_r(&uniform_keys, &r_bytes);
                if key_valid_bits & 1 != 0 {
                    uniform_decoded_key = Some(CachedPublicKey {
                        encoded: first_public_key,
                        table: tables.into_iter().next().unwrap(),
                    });
                }
                decoded_r = Some((r_points, lane_flags_from_mask(r_valid_bits)));
            }
        } else {
            let chunk_cached_keys: [Option<&CachedPublicKey>; SIMD_LANES] =
                core::array::from_fn(|lane| self.cache.get(&public_keys[lane]));
            lane = 0;
            while lane < SIMD_LANES {
                if chunk_cached_keys[lane].is_none() {
                    missing_key_lanes[lane] = true;
                }
                lane += 1;
            }
            cached_keys = Some(chunk_cached_keys);

            if any_lane(&missing_key_lanes) {
                let (tables, key_valid_bits, r_points, r_valid_bits) =
                    avx512ifma::decode_keys_and_decompress_r(&public_keys, &r_bytes);
                let mut tables = tables.into_iter();
                decoded_keys = Some((
                    core::array::from_fn(|lane| CachedPublicKey {
                        encoded: public_keys[lane],
                        table: tables.next().unwrap(),
                    }),
                    lane_flags_from_mask(key_valid_bits),
                ));
                decoded_r = Some((r_points, lane_flags_from_mask(r_valid_bits)));
            }
        }

        let mut messages = [inputs[0].message; SIMD_LANES];
        lane = 1;
        while lane < SIMD_LANES {
            messages[lane] = inputs[lane].message;
            lane += 1;
        }
        let digests = sha512::hash_ed25519_challenges(&r_bytes, &public_keys, messages);

        let mut k_digits: [Radix16; SIMD_LANES] = [[0i8; 64]; SIMD_LANES];
        lane = 0;
        while lane < SIMD_LANES {
            k_digits[lane] = Scalar::from_wide_bytes(digests[lane]).to_radix16();
            lane += 1;
        }

        {
            let mut public_key_tables: [&PointTable; SIMD_LANES] =
                [&self.identity_table; SIMD_LANES];
            if uniform_public_key {
                if let Some(key) = uniform_cached_key {
                    public_key_tables = [&key.table; SIMD_LANES];
                } else if let Some(key) = &uniform_decoded_key {
                    // `uniform_decoded_key` is always built from `first_public_key`
                    // (see below), so its `encoded` field is guaranteed to match.
                    public_key_tables = [&key.table; SIMD_LANES];
                } else {
                    valid = [false; SIMD_LANES];
                }
            } else {
                let cached_keys = cached_keys
                    .as_ref()
                    .expect("non-uniform chunks are looked up");
                lane = 0;
                while lane < SIMD_LANES {
                    if let Some(key) = cached_keys[lane] {
                        public_key_tables[lane] = &key.table;
                    } else if let Some((keys, key_valid_lanes)) = &decoded_keys {
                        if key_valid_lanes[lane] {
                            public_key_tables[lane] = &keys[lane].table;
                        } else {
                            valid[lane] = false;
                        }
                    } else {
                        valid[lane] = false;
                    }
                    lane += 1;
                }
            }

            let prepared = PreparedBatch {
                public_key_tables,
                s_digits,
                k_digits,
            };
            match policy {
                VerifyPolicy::Zip215 => {
                    let (r_points, r_valid_lanes) = match decoded_r {
                        Some(decoded) => decoded,
                        None => {
                            let (r_points, r_mask) = avx512ifma::decompress_r_points(&r_bytes);
                            (r_points, lane_flags_from_mask(r_mask))
                        }
                    };
                    let simd =
                        avx512ifma::verify_prepared_zip215(&prepared, &r_points, self.base_table);
                    lane = 0;
                    while lane < SIMD_LANES {
                        out[lane] = simd[lane] && valid[lane] && r_valid_lanes[lane];
                        lane += 1;
                    }
                }
                VerifyPolicy::Dalek => {
                    if let Some((r_points, r_valid_lanes)) = decoded_r {
                        let simd = avx512ifma::verify_prepared_dalek_projective(
                            &prepared,
                            &r_points,
                            self.base_table,
                        );
                        // Dalek requires an exact canonical `R`, not just an
                        // affine match: re-encode the decompressed point and
                        // require a byte-for-byte match against the input, so
                        // a non-canonical encoding that happens to decode to
                        // the same point (e.g. a set sign bit on `x == 0`) is
                        // rejected exactly as the raw-byte comparison below
                        // would reject it.
                        let r_canonical = r_points.compress();
                        lane = 0;
                        while lane < SIMD_LANES {
                            out[lane] = simd[lane]
                                && valid[lane]
                                && r_valid_lanes[lane]
                                && r_canonical[lane] == r_bytes[lane]
                                && !dalek_legacy_excluded(&public_keys[lane], &r_bytes[lane]);
                            lane += 1;
                        }
                    } else {
                        let simd = avx512ifma::verify_prepared_dalek(
                            &prepared,
                            &r_bytes,
                            self.base_table,
                        );
                        lane = 0;
                        while lane < SIMD_LANES {
                            out[lane] = simd[lane]
                                && valid[lane]
                                && !dalek_legacy_excluded(&public_keys[lane], &r_bytes[lane]);
                            lane += 1;
                        }
                    }
                }
            }
        }

        if let Some(key) = uniform_decoded_key {
            // Only ever constructed after a cache miss set every lane in
            // `missing_key_lanes`, so inserting here is always warranted.
            self.cache.insert(key);
        }
        if let Some((keys, key_valid_lanes)) = decoded_keys {
            for (lane, key) in keys.into_iter().enumerate() {
                if missing_key_lanes[lane] && key_valid_lanes[lane] {
                    self.cache.insert(key);
                }
            }
        }
    }
}

fn dalek_legacy_excluded(public_key: &[u8; 32], r_bytes: &[u8; 32]) -> bool {
    *public_key == [0u8; 32] || r_encoding_is_legacy_excluded(r_bytes)
}

fn lane_flags_from_mask(mask: u8) -> [bool; SIMD_LANES] {
    core::array::from_fn(|lane| lane < u8::BITS as usize && mask & (1u8 << lane) != 0)
}

fn any_lane(lanes: &[bool; SIMD_LANES]) -> bool {
    lanes.iter().any(|&lane| lane)
}
