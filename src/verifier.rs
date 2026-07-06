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

// The base-point table (all 273 precomputed multiples used by the multi-scalar
// ladder, ~43KB) is identical for every `Verifier` regardless of policy or
// cache choice, so it's built once per process and shared by reference rather
// than reconstructed (135 point doublings/additions) for every instance.
static BASE_TABLE: LazyLock<BasepointTable> = LazyLock::new(BasepointTable::new);

// Same reasoning as `BASE_TABLE`: the identity-point placeholder table used
// for invalid/missing lanes is identical for every `Verifier`, so it's shared
// by reference instead of rebuilt (17 `CachedPoint`s) per instance.
static IDENTITY_TABLE: LazyLock<PointTable> =
    LazyLock::new(|| PointTable::new(&EdwardsPoint::identity()));

struct ChunkParts<'a> {
    valid: [bool; SIMD_LANES],
    r_bytes: [[u8; 32]; SIMD_LANES],
    public_keys: [[u8; 32]; SIMD_LANES],
    s_digits: [Radix16; SIMD_LANES],
    messages: [&'a [u8]; SIMD_LANES],
}

/// Batch Ed25519 signature verifier for a fixed [`VerifyPolicy`] and
/// [`KeyCache`]. Construction is not free (it builds/shares the base-point
/// table and validates AVX-512 support), so build one and reuse it across
/// calls to [`verify_batch`](Verifier::verify_batch).
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
    /// Panics if this binary was not built with the AVX-512 features this
    /// crate requires enabled for the running CPU; see the crate-level
    /// [Requirements](crate#requirements) section.
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
    /// Create a verifier backed by a caller-provided cache. Use
    /// [`HotKeyCache::with_capacity`](crate::HotKeyCache::with_capacity) for
    /// a capacity-bounded evictable cache:
    /// `Verifier::with_cache(policy, HotKeyCache::with_capacity(n))`.
    ///
    /// # Panics
    ///
    /// Panics if this binary was not built with the AVX-512 features this
    /// crate requires enabled for the running CPU; see the crate-level
    /// [Requirements](crate#requirements) section. This is a guard against a
    /// bare `SIGILL`, not a complete one — see that section for why.
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
        let mut missing_key_lanes = [false; SIMD_LANES];
        let mut lane = 0;
        while lane < SIMD_LANES {
            missing_key_lanes[lane] = cached_keys[lane].is_none();
            lane += 1;
        }

        let mut decoded_r: Option<(avx512ifma::WideRPoints, [bool; SIMD_LANES])> = None;
        let mut decoded_key_tables: Option<([PointTable; SIMD_LANES], [bool; SIMD_LANES])> = None;
        if any_lane(&missing_key_lanes) {
            let (tables, key_valid_bits, r_points, r_valid_bits) =
                avx512ifma::decode_keys_and_decompress_r(&public_keys, &r_bytes);
            decoded_key_tables = Some((tables, lane_flags_from_mask(key_valid_bits)));
            decoded_r = Some((r_points, lane_flags_from_mask(r_valid_bits)));
        }

        let mut public_key_tables: [&PointTable; SIMD_LANES] = [self.identity_table; SIMD_LANES];
        lane = 0;
        while lane < SIMD_LANES {
            if let Some(key) = cached_keys[lane] {
                public_key_tables[lane] = &key.table;
            } else if let Some((tables, key_valid_lanes)) = &decoded_key_tables {
                if key_valid_lanes[lane] {
                    public_key_tables[lane] = &tables[lane];
                } else {
                    valid[lane] = false;
                }
            } else {
                valid[lane] = false;
            }
            lane += 1;
        }
        if !any_lane(&valid) {
            return;
        }

        let k_digits = challenge_digits(&r_bytes, &public_keys, messages);

        let prepared = PreparedBatch {
            public_key_tables,
            s_digits: &s_digits,
            k_digits: &k_digits,
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
                    let r_x_zero = r_points.x_zero_lanes();
                    lane = 0;
                    while lane < SIMD_LANES {
                        let signed_zero = r_x_zero[lane] && r_bytes[lane][31] & 0x80 != 0;
                        out[lane] = simd[lane]
                            && valid[lane]
                            && r_valid_lanes[lane]
                            && r_encoding_has_canonical_y(&r_bytes[lane])
                            && !signed_zero
                            && !dalek_legacy_excluded(&public_keys[lane], &r_bytes[lane]);
                        lane += 1;
                    }
                } else {
                    let simd =
                        avx512ifma::verify_prepared_dalek(&prepared, &r_bytes, self.base_table);
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
}

#[inline(always)]
fn parse_chunk_inputs<'a>(inputs: &[VerifyInput<'a>; SIMD_LANES]) -> ChunkParts<'a> {
    let mut valid = [true; SIMD_LANES];
    let mut r_bytes = [[0u8; 32]; SIMD_LANES];
    let mut public_keys = [[0u8; 32]; SIMD_LANES];
    let mut s_digits = [[0i8; 64]; SIMD_LANES];
    let mut messages = [inputs[0].message; SIMD_LANES];
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
        messages[lane] = inputs[lane].message;
        lane += 1;
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
    r_bytes: &[[u8; 32]; SIMD_LANES],
    public_keys: &[[u8; 32]; SIMD_LANES],
    messages: [&[u8]; SIMD_LANES],
) -> [Radix16; SIMD_LANES] {
    let digests = sha512::hash_ed25519_challenge_words(r_bytes, public_keys, messages);
    core::array::from_fn(|lane| Scalar::from_wide_words(digests[lane]).to_radix16())
}

fn dalek_legacy_excluded(public_key: &[u8; 32], r_bytes: &[u8; 32]) -> bool {
    *public_key == [0u8; 32] || r_encoding_is_legacy_excluded(r_bytes)
}

fn lane_flags_from_mask(mask: u8) -> [bool; SIMD_LANES] {
    // `SIMD_LANES == 8` is const-asserted in `wide.rs`, so every lane index
    // is in range for a `u8` mask without a bounds guard.
    core::array::from_fn(|lane| mask & (1u8 << lane) != 0)
}

fn any_lane(lanes: &[bool; SIMD_LANES]) -> bool {
    lanes.iter().any(|&lane| lane)
}
