use crate::batch::{self, PreparedChunk};
use crate::cache::{CachedPublicKey, KeyCache, NullKeyCache};
use crate::edwards::{BasepointTable, BasepointTableEntries, PointTable};
use crate::policy::{VerifyPolicy, r_encoding_has_canonical_y, r_encoding_is_legacy_excluded};
use crate::scalar::{self, Radix16, Scalar};
use crate::sha512;
use crate::wide::avx512ifma;
use std::sync::LazyLock;

/// One public key, signature, and message to verify.
#[derive(Clone, Copy, Debug)]
pub struct VerifyInput<'a> {
    /// Encoded Ed25519 public key.
    pub public_key: [u8; 32],
    /// Encoded Ed25519 signature (`R || S`).
    pub signature: [u8; 64],
    /// The signed message.
    pub message: &'a [u8],
}

const SIMD_LANES: usize = batch::SIMD_LANES;
const R_ENCODING_LEN: usize = batch::R_ENCODING_LEN;

// `VerifyInput` spells these as literals for rustdoc's sake; pin them here.
const _: () = assert!(batch::PUBLIC_KEY_LEN == 32);
const _: () = assert!(batch::SIGNATURE_LEN == 64);

// Shared once per process; the base-point table is policy- and cache-independent.
static BASE_TABLE: LazyLock<BasepointTable> = LazyLock::new(BasepointTable::new);

// Placeholder table for invalid/missing lanes, also shared across verifiers.
static IDENTITY_TABLE: LazyLock<PointTable> = LazyLock::new(PointTable::cold_identity);

struct ParsedChunk<'a> {
    valid: [bool; SIMD_LANES],
    r_bytes: [[u8; R_ENCODING_LEN]; SIMD_LANES],
    public_keys: [[u8; batch::PUBLIC_KEY_LEN]; SIMD_LANES],
    s_digits: [Radix16; SIMD_LANES],
    messages: [&'a [u8]; SIMD_LANES],
}

/// Everything needed to score one deferred Dalek chunk once its recomputed
/// `R` encoding is available. The candidate itself is queued separately so the
/// batch inversion sees a contiguous slice.
#[derive(Debug)]
struct PendingDalekChunk {
    valid: [bool; SIMD_LANES],
    r_bytes: [[u8; R_ENCODING_LEN]; SIMD_LANES],
    public_keys: [[u8; batch::PUBLIC_KEY_LEN]; SIMD_LANES],
    output_indices: [usize; SIMD_LANES],
    active_lane_count: usize,
}

/// The per-lane chunk data both policies score their SIMD result against.
struct ScoredLanes<'a> {
    r_bytes: &'a [[u8; R_ENCODING_LEN]; SIMD_LANES],
    public_keys: &'a [[u8; batch::PUBLIC_KEY_LEN]; SIMD_LANES],
    valid: &'a [bool; SIMD_LANES],
}

#[derive(Debug)]
struct ChunkScratch {
    key_tables: [Option<PointTable>; SIMD_LANES],
}

impl ChunkScratch {
    fn new() -> Self {
        Self {
            key_tables: core::array::from_fn(|_| None),
        }
    }
}

/// Batch Ed25519 verifier for a fixed [`VerifyPolicy`] and [`KeyCache`].
/// Reuse one across [`verify_batch`](Verifier::verify_batch) calls.
#[derive(Debug)]
pub struct Verifier<C: KeyCache = NullKeyCache> {
    policy: VerifyPolicy,
    base_table: &'static BasepointTableEntries,
    // Invalid lanes are masked out but still need a real ladder table.
    identity_table: &'static PointTable,
    bucket_order: Vec<usize>,
    dalek_candidates: Vec<avx512ifma::DalekCandidate>,
    dalek_pending: Vec<PendingDalekChunk>,
    scratch: Box<ChunkScratch>,
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

impl<C: KeyCache> Verifier<C> {
    /// Create a verifier backed by a caller-provided cache. For a bounded cache:
    /// `Verifier::with_cache(policy, HotKeyCache::with_capacity(n))`.
    pub fn with_cache(policy: VerifyPolicy, cache: C) -> Self {
        Self {
            policy,
            base_table: BASE_TABLE.entries(),
            identity_table: &*IDENTITY_TABLE,
            bucket_order: Vec::new(),
            dalek_candidates: Vec::new(),
            dalek_pending: Vec::new(),
            scratch: Box::new(ChunkScratch::new()),
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

    /// Verify a batch and write one boolean result per input. `out[i]` is
    /// `true` iff `inputs[i]`'s signature is valid for its `(public_key, message)`.
    ///
    /// # Panics
    ///
    /// Panics if `inputs.len() != out.len()`.
    pub fn verify_batch(&mut self, inputs: &[VerifyInput<'_>], out: &mut [bool]) {
        assert_eq!(inputs.len(), out.len());
        let mut bucket_order = core::mem::take(&mut self.bucket_order);
        let mut candidates = core::mem::take(&mut self.dalek_candidates);
        let mut pending = core::mem::take(&mut self.dalek_pending);
        batch::for_each_simd_chunk(
            inputs,
            &mut bucket_order,
            |chunk, output_indices, active_lane_count| {
                let mut tmp = [false; SIMD_LANES];
                let deferred = self.verify_chunk(
                    chunk,
                    *output_indices,
                    active_lane_count,
                    &mut tmp,
                    &mut candidates,
                    &mut pending,
                );
                if !deferred {
                    for (&index, &value) in output_indices[..active_lane_count].iter().zip(&tmp) {
                        out[index] = value;
                    }
                } else if candidates.len() == avx512ifma::DALEK_BATCH {
                    flush_dalek_queue(&mut candidates, &mut pending, out);
                }
            },
        );
        flush_dalek_queue(&mut candidates, &mut pending, out);
        self.bucket_order = bucket_order;
        self.dalek_candidates = candidates;
        self.dalek_pending = pending;
    }

    /// Verify one chunk, returning whether its Dalek result was queued for a
    /// shared inversion instead of scored here. Queuing writes straight into
    /// the caller's buffers: returning the candidate by value would put a
    /// kilobyte of `sret` traffic on every chunk, including the paths that
    /// never defer.
    fn verify_chunk(
        &mut self,
        inputs: &[VerifyInput<'_>; SIMD_LANES],
        output_indices: [usize; SIMD_LANES],
        active_lane_count: usize,
        out: &mut [bool; SIMD_LANES],
        candidates: &mut Vec<avx512ifma::DalekCandidate>,
        pending: &mut Vec<PendingDalekChunk>,
    ) -> bool {
        let policy = self.policy;

        let ParsedChunk {
            mut valid,
            r_bytes,
            public_keys,
            s_digits,
            messages,
        } = parse_chunk_inputs(inputs);
        if !any_lane(&valid) {
            return false;
        }

        let cached_keys: [Option<&CachedPublicKey>; SIMD_LANES] =
            core::array::from_fn(|lane| self.cache.get(&public_keys[lane]));
        let missing_key_lanes: [bool; SIMD_LANES] =
            core::array::from_fn(|lane| cached_keys[lane].is_none());

        // Decode missing keys and their R points together.
        let mut decoded_r: Option<(avx512ifma::WideRPoint, [bool; SIMD_LANES])> = None;
        let mut decoded_key_lanes = [false; SIMD_LANES];
        if any_lane(&missing_key_lanes) {
            let (key_valid_bits, r_points, r_valid_bits) = avx512ifma::decode_keys_and_decompress_r(
                &public_keys,
                &r_bytes,
                policy == VerifyPolicy::Dalek,
                &mut self.scratch.key_tables,
            );
            decoded_key_lanes = avx512ifma::mask_to_lanes(key_valid_bits);
            decoded_r = Some((r_points, avx512ifma::mask_to_lanes(r_valid_bits)));
        }

        let public_key_tables: [&PointTable; SIMD_LANES] = core::array::from_fn(|lane| {
            if let Some(key) = cached_keys[lane] {
                &key.table
            } else {
                // Cache misses populate `self.scratch.key_tables` above.
                if decoded_key_lanes[lane] {
                    self.scratch.key_tables[lane]
                        .as_ref()
                        .expect("a valid decoded lane has a table")
                } else {
                    valid[lane] = false;
                    self.identity_table
                }
            }
        });

        // Skip the ladder, but still retain the keys that did decode.
        let mut deferred = false;
        if any_lane(&valid) {
            let k_digits = challenge_digits(&r_bytes, &public_keys, messages);

            let prepared = PreparedChunk {
                public_key_tables,
                s_digits: &s_digits,
                k_digits: &k_digits,
            };
            let lanes = ScoredLanes {
                r_bytes: &r_bytes,
                public_keys: &public_keys,
                valid: &valid,
            };
            match policy {
                VerifyPolicy::Zip215 => self.verify_zip215_lanes(&prepared, decoded_r, &lanes, out),
                VerifyPolicy::Dalek => {
                    deferred =
                        self.verify_dalek_lanes(&prepared, decoded_r, &lanes, out, candidates);
                    if deferred {
                        pending.push(PendingDalekChunk {
                            valid,
                            r_bytes,
                            public_keys,
                            output_indices,
                            active_lane_count,
                        });
                    }
                }
            }
        }

        self.retain_decoded_keys(&missing_key_lanes, &decoded_key_lanes, &public_keys);
        deferred
    }

    /// Offer freshly decoded tables to the cache, emptying the scratch slots.
    fn retain_decoded_keys(
        &mut self,
        missing_key_lanes: &[bool; SIMD_LANES],
        decoded_key_lanes: &[bool; SIMD_LANES],
        public_keys: &[[u8; batch::PUBLIC_KEY_LEN]; SIMD_LANES],
    ) {
        // Only a decode fills slots, and it runs exactly when a lane missed.
        if !any_lane(missing_key_lanes) {
            return;
        }
        for lane in 0..SIMD_LANES {
            let table = self.scratch.key_tables[lane]
                .take()
                .expect("a decode fills every lane's slot");
            if missing_key_lanes[lane] && decoded_key_lanes[lane] {
                self.cache.insert(CachedPublicKey {
                    encoded: public_keys[lane],
                    table,
                });
            }
        }
    }

    #[inline(always)]
    fn verify_zip215_lanes(
        &self,
        prepared: &PreparedChunk<'_>,
        decoded_r: Option<(avx512ifma::WideRPoint, [bool; SIMD_LANES])>,
        lanes: &ScoredLanes<'_>,
        out: &mut [bool; SIMD_LANES],
    ) {
        // Cache misses already decompressed R alongside their keys.
        let (r_points, r_valid_lanes) = match decoded_r {
            Some(decoded) => decoded,
            None => {
                let (r_points, r_mask) = avx512ifma::decompress_r_points(lanes.r_bytes);
                (r_points, avx512ifma::mask_to_lanes(r_mask))
            }
        };

        let equation_holds =
            avx512ifma::verify_prepared_zip215(prepared, &r_points, self.base_table);
        for lane in 0..SIMD_LANES {
            out[lane] = equation_holds[lane] && lanes.valid[lane] && r_valid_lanes[lane];
        }
    }

    /// Score the lanes against an already-decompressed `R`, or queue the point
    /// when `R` is still encoded so the recompression can share an inversion.
    /// Returns whether the chunk was queued.
    #[inline(always)]
    fn verify_dalek_lanes(
        &self,
        prepared: &PreparedChunk<'_>,
        decoded_r: Option<(avx512ifma::WideRPoint, [bool; SIMD_LANES])>,
        lanes: &ScoredLanes<'_>,
        out: &mut [bool; SIMD_LANES],
        candidates: &mut Vec<avx512ifma::DalekCandidate>,
    ) -> bool {
        let Some((r_points, r_valid_lanes)) = decoded_r else {
            // Every lane hit the cache, so nothing decompressed `R`. Recomputing
            // it needs an inversion; queue the point to be batched instead.
            candidates.push(avx512ifma::prepare_dalek_candidate(
                prepared,
                self.base_table,
            ));
            return true;
        };

        // R already decompressed on a cache miss: compare points directly.
        let equation_holds =
            avx512ifma::verify_prepared_dalek_decompressed_r(prepared, &r_points, self.base_table);
        let r_x_zero = r_points.x_zero_lanes();
        for lane in 0..SIMD_LANES {
            let r_bytes = &lanes.r_bytes[lane];
            let signed_zero = r_x_zero[lane] && r_bytes[31] & 0x80 != 0;
            out[lane] = equation_holds[lane]
                && lanes.valid[lane]
                && r_valid_lanes[lane]
                && r_encoding_has_canonical_y(r_bytes)
                && !signed_zero
                && !dalek_legacy_excluded(&lanes.public_keys[lane], r_bytes);
        }
        false
    }
}

/// Compress every queued candidate through one shared inversion and score the
/// chunks against their encoded `R`. Leaves both queues empty.
fn flush_dalek_queue(
    candidates: &mut Vec<avx512ifma::DalekCandidate>,
    pending: &mut Vec<PendingDalekChunk>,
    out: &mut [bool],
) {
    debug_assert_eq!(candidates.len(), pending.len());
    if candidates.is_empty() {
        return;
    }

    let mut encodings = [[[0u8; R_ENCODING_LEN]; SIMD_LANES]; avx512ifma::DALEK_BATCH];
    avx512ifma::compress_dalek_candidates(candidates, &mut encodings[..candidates.len()]);

    for (chunk, encoding) in pending.drain(..).zip(&encodings) {
        for lane in 0..chunk.active_lane_count {
            // Recompression is canonical, so a non-canonical or wrong-sign `R`
            // encoding simply fails to match; only the legacy filter is extra.
            out[chunk.output_indices[lane]] = encoding[lane] == chunk.r_bytes[lane]
                && chunk.valid[lane]
                && !dalek_legacy_excluded(&chunk.public_keys[lane], &chunk.r_bytes[lane]);
        }
    }
    candidates.clear();
}

#[inline(always)]
fn parse_chunk_inputs<'a>(inputs: &[VerifyInput<'a>; SIMD_LANES]) -> ParsedChunk<'a> {
    let mut valid = [true; SIMD_LANES];
    let mut r_bytes = [[0u8; R_ENCODING_LEN]; SIMD_LANES];
    let mut public_keys = [[0u8; batch::PUBLIC_KEY_LEN]; SIMD_LANES];
    let mut s_digits = [[0i8; 64]; SIMD_LANES];
    let mut messages = [inputs[0].message; SIMD_LANES];
    for (lane, input) in inputs.iter().enumerate() {
        r_bytes[lane].copy_from_slice(&input.signature[..R_ENCODING_LEN]);

        let mut s_bytes = [0u8; 32];
        s_bytes.copy_from_slice(&input.signature[R_ENCODING_LEN..]);
        if scalar::is_canonical(&s_bytes) {
            s_digits[lane] = Scalar::from_canonical_bytes(s_bytes).to_radix16();
        } else {
            valid[lane] = false;
        }
        public_keys[lane] = input.public_key;
        messages[lane] = input.message;
    }

    ParsedChunk {
        valid,
        r_bytes,
        public_keys,
        s_digits,
        messages,
    }
}

#[inline(always)]
fn challenge_digits(
    r_bytes: &[[u8; R_ENCODING_LEN]; SIMD_LANES],
    public_keys: &[[u8; batch::PUBLIC_KEY_LEN]; SIMD_LANES],
    messages: [&[u8]; SIMD_LANES],
) -> [Radix16; SIMD_LANES] {
    let digests = sha512::hash_ed25519_challenge_words(r_bytes, public_keys, messages);
    scalar::wide_words_to_radix16(&digests)
}

fn dalek_legacy_excluded(
    public_key: &[u8; batch::PUBLIC_KEY_LEN],
    r_bytes: &[u8; R_ENCODING_LEN],
) -> bool {
    *public_key == [0u8; batch::PUBLIC_KEY_LEN] || r_encoding_is_legacy_excluded(r_bytes)
}

fn any_lane(lanes: &[bool; SIMD_LANES]) -> bool {
    lanes.iter().any(|&lane| lane)
}
