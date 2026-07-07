use crate::batch::{self, PreparedBatch};
use crate::cache::{CachedPublicKey, KeyCache, NullKeyCache};
use crate::cpuid;
use crate::edwards::{BasepointTable, EdwardsPoint, PointTable};
use crate::policy::{VerifyPolicy, r_encoding_has_canonical_y, r_encoding_is_legacy_excluded};
use crate::scalar::{self, Radix16, Scalar};
use crate::sha512;
use crate::wide::avx512ifma;
use std::sync::LazyLock;

/// One signature verification request: a public key, a signature over
/// `message`, and the message itself.
#[derive(Clone, Copy, Debug)]
pub struct VerifyInput<'a> {
    /// Encoded Ed25519 public key.
    pub public_key: [u8; batch::PUBLIC_KEY_LEN],
    /// Encoded Ed25519 signature (`R || S`).
    pub signature: [u8; batch::SIGNATURE_LEN],
    /// The signed message.
    pub message: &'a [u8],
}

const SIMD_LANES: usize = batch::SIMD_LANES;
const R_ENCODING_LEN: usize = batch::R_ENCODING_LEN;

// Shared once per process; the base-point table is policy- and cache-independent.
static BASE_TABLE: LazyLock<BasepointTable> = LazyLock::new(BasepointTable::new);

// Placeholder table for invalid/missing lanes, also shared across verifiers.
static IDENTITY_TABLE: LazyLock<PointTable> =
    LazyLock::new(|| PointTable::new(&EdwardsPoint::identity()));

struct ChunkParts<'a> {
    valid: [bool; SIMD_LANES],
    r_bytes: [[u8; R_ENCODING_LEN]; SIMD_LANES],
    public_keys: [[u8; batch::PUBLIC_KEY_LEN]; SIMD_LANES],
    s_digits: [Radix16; SIMD_LANES],
    messages: [&'a [u8]; SIMD_LANES],
}

/// Batch Ed25519 verifier for a fixed [`VerifyPolicy`] and [`KeyCache`].
/// Reuse one across [`verify_batch`](Verifier::verify_batch) calls.
#[derive(Debug)]
pub struct Verifier<C: KeyCache = NullKeyCache> {
    policy: VerifyPolicy,
    base_table: &'static BasepointTable,
    // Placeholder table for lanes whose key failed decode/lookup; results for
    // those lanes are masked out via `valid`, so its contents never affect
    // the output, but the multiscalar ladder still needs a real table.
    identity_table: &'static PointTable,
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
    ///
    /// # Panics
    ///
    /// Panics if required AVX-512 support is unavailable.
    pub fn new() -> Self {
        Self::with_policy(VerifyPolicy::default())
    }

    /// Create a verifier with a specific policy and no retained-key cache.
    ///
    /// # Panics
    ///
    /// Panics under the same condition as [`Verifier::new`].
    pub fn with_policy(policy: VerifyPolicy) -> Self {
        Self::with_cache(policy, NullKeyCache::new())
    }
}

impl<C: KeyCache> Verifier<C> {
    /// Create a verifier backed by a caller-provided cache. For a bounded cache:
    /// `Verifier::with_cache(policy, HotKeyCache::with_capacity(n))`.
    ///
    /// # Panics
    ///
    /// Panics if required AVX-512 support is unavailable.
    pub fn with_cache(policy: VerifyPolicy, cache: C) -> Self {
        cpuid::assert_required_avx512_runtime_support();
        Self {
            policy,
            base_table: &*BASE_TABLE,
            identity_table: &*IDENTITY_TABLE,
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

    /// Verify a batch and write one boolean result per input. `out[i]` is
    /// `true` iff `inputs[i]`'s signature is valid for its `(public_key, message)`.
    ///
    /// # Panics
    ///
    /// Panics if `inputs.len() != out.len()`.
    pub fn verify_batch(&mut self, inputs: &[VerifyInput<'_>], out: &mut [bool]) {
        assert_eq!(inputs.len(), out.len());
        let mut bucket_order = core::mem::take(&mut self.bucket_order);
        batch::for_each_simd_chunk(inputs, &mut bucket_order, |chunk, output_indices, lanes| {
            let mut tmp = [false; SIMD_LANES];
            self.try_verify_chunk(chunk, &mut tmp);

            for (&index, &value) in output_indices[..lanes].iter().zip(&tmp) {
                out[index] = value;
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

        let ChunkParts {
            mut valid,
            r_bytes,
            public_keys,
            s_digits,
            messages,
        } = parse_chunk_inputs(inputs);
        if !any_lane(&valid) {
            return;
        }

        let cached_keys: [Option<&CachedPublicKey>; SIMD_LANES] =
            core::array::from_fn(|lane| self.cache.get(&public_keys[lane]));
        let missing_key_lanes: [bool; SIMD_LANES] =
            core::array::from_fn(|lane| cached_keys[lane].is_none());

        // Decode uncached public keys and batch the R decompression only when a lane missed the cache.
        let mut decoded_r: Option<(avx512ifma::WideRPoints, [bool; SIMD_LANES])> = None;
        let mut decoded_key_tables: Option<([PointTable; SIMD_LANES], [bool; SIMD_LANES])> = None;
        if any_lane(&missing_key_lanes) {
            let (tables, key_valid_bits, r_points, r_valid_bits) =
                avx512ifma::decode_keys_and_decompress_r(&public_keys, &r_bytes);
            decoded_key_tables = Some((tables, lane_flags_from_mask(key_valid_bits)));
            decoded_r = Some((r_points, lane_flags_from_mask(r_valid_bits)));
        }

        // Build per-lane public key tables from cache hits or freshly decoded misses.
        let public_key_tables: [&PointTable; SIMD_LANES] = core::array::from_fn(|lane| {
            if let Some(key) = cached_keys[lane] {
                &key.table
            } else {
                // Cache misses populate `decoded_key_tables` above.
                let (tables, key_valid_lanes) = decoded_key_tables
                    .as_ref()
                    .expect("a cache miss always triggers a decode");
                if key_valid_lanes[lane] {
                    &tables[lane]
                } else {
                    valid[lane] = false;
                    self.identity_table
                }
            }
        });
        // Stop if every lane failed public-key validation.
        if !any_lane(&valid) {
            return;
        }

        // Build shared challenge digits before dispatching to the policy-specific verifier.
        let k_digits = challenge_digits(&r_bytes, &public_keys, messages);

        let prepared = PreparedBatch {
            public_key_tables,
            s_digits: &s_digits,
            k_digits: &k_digits,
        };
        match policy {
            VerifyPolicy::Zip215 => {
                self.verify_zip215_lanes(&prepared, decoded_r, &r_bytes, &valid, out)
            }
            VerifyPolicy::Dalek => {
                self.verify_dalek_lanes(&prepared, decoded_r, &r_bytes, &public_keys, &valid, out)
            }
        }

        // Try to insert any recently decoded keys into the cache.
        if let Some((tables, key_valid_lanes)) = decoded_key_tables {
            for (lane, table) in tables.into_iter().enumerate() {
                if missing_key_lanes[lane] && key_valid_lanes[lane] {
                    self.cache.insert(CachedPublicKey {
                        encoded: public_keys[lane],
                        table,
                    });
                }
            }
        }
    }

    #[inline(always)]
    fn verify_zip215_lanes(
        &self,
        prepared: &PreparedBatch<'_>,
        decoded_r: Option<(avx512ifma::WideRPoints, [bool; SIMD_LANES])>,
        r_bytes: &[[u8; R_ENCODING_LEN]; SIMD_LANES],
        valid: &[bool; SIMD_LANES],
        out: &mut [bool; SIMD_LANES],
    ) {
        // Reuse the R points decompressed above on a cache miss; decompress them here otherwise.
        let (r_points, r_valid_lanes) = match decoded_r {
            Some(decoded) => decoded,
            None => {
                let (r_points, r_mask) = avx512ifma::decompress_r_points(r_bytes);
                (r_points, lane_flags_from_mask(r_mask))
            }
        };

        // Run the batched verification equation, then mask with per-lane input/R validity.
        let simd = avx512ifma::verify_prepared_zip215(prepared, &r_points, self.base_table);
        for lane in 0..SIMD_LANES {
            out[lane] = simd[lane] && valid[lane] && r_valid_lanes[lane];
        }
    }

    #[inline(always)]
    fn verify_dalek_lanes(
        &self,
        prepared: &PreparedBatch<'_>,
        decoded_r: Option<(avx512ifma::WideRPoints, [bool; SIMD_LANES])>,
        r_bytes: &[[u8; R_ENCODING_LEN]; SIMD_LANES],
        public_keys: &[[u8; batch::PUBLIC_KEY_LEN]; SIMD_LANES],
        valid: &[bool; SIMD_LANES],
        out: &mut [bool; SIMD_LANES],
    ) {
        if let Some((r_points, r_valid_lanes)) = decoded_r {
            // R already decompressed on a cache miss: compare points directly.
            let simd =
                avx512ifma::verify_prepared_dalek_projective(prepared, &r_points, self.base_table);
            let r_x_zero = r_points.x_zero_lanes();
            for lane in 0..SIMD_LANES {
                let signed_zero = r_x_zero[lane] && r_bytes[lane][31] & 0x80 != 0;
                out[lane] = simd[lane]
                    && valid[lane]
                    && r_valid_lanes[lane]
                    && r_encoding_has_canonical_y(&r_bytes[lane])
                    && !signed_zero
                    && !dalek_legacy_excluded(&public_keys[lane], &r_bytes[lane]);
            }
        } else {
            // All cache hits, nothing decompressed yet: recompute R and compare bytes.
            let simd = avx512ifma::verify_prepared_dalek(prepared, r_bytes, self.base_table);
            for lane in 0..SIMD_LANES {
                out[lane] = simd[lane]
                    && valid[lane]
                    && !dalek_legacy_excluded(&public_keys[lane], &r_bytes[lane]);
            }
        }
    }
}

#[inline(always)]
fn parse_chunk_inputs<'a>(inputs: &[VerifyInput<'a>; SIMD_LANES]) -> ChunkParts<'a> {
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

    ChunkParts {
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
    core::array::from_fn(|lane| Scalar::from_wide_words(digests[lane]).to_radix16())
}

fn dalek_legacy_excluded(
    public_key: &[u8; batch::PUBLIC_KEY_LEN],
    r_bytes: &[u8; R_ENCODING_LEN],
) -> bool {
    *public_key == [0u8; batch::PUBLIC_KEY_LEN] || r_encoding_is_legacy_excluded(r_bytes)
}

fn lane_flags_from_mask(mask: u8) -> [bool; SIMD_LANES] {
    // `SIMD_LANES == 8`, so every lane fits in this `u8` mask.
    core::array::from_fn(|lane| mask & (1u8 << lane) != 0)
}

fn any_lane(lanes: &[bool; SIMD_LANES]) -> bool {
    lanes.iter().any(|&lane| lane)
}
