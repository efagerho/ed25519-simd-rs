use crate::batch::{self, PreparedBatch, PreparedSplitBatch};
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

// Phase 2h: B′ = [2¹²⁷]B for the split ladder's s₁ digits — same 273-entry
// affine layout as BASE_TABLE (~33 KB), policy- and cache-independent.
static BASE_TABLE_PRIME: LazyLock<BasepointTable> =
    LazyLock::new(|| BasepointTable::from_point(&EdwardsPoint::basepoint().mul_by_pow2_127()));

// Placeholder table for invalid/missing lanes, also shared across verifiers.
static IDENTITY_TABLE: LazyLock<PointTable> =
    LazyLock::new(|| PointTable::new(&EdwardsPoint::identity()));

struct ChunkParts<'a> {
    valid: [bool; SIMD_LANES],
    r_bytes: [[u8; R_ENCODING_LEN]; SIMD_LANES],
    public_keys: [[u8; batch::PUBLIC_KEY_LEN]; SIMD_LANES],
    s_digits: [Radix16; SIMD_LANES],
    /// The canonical scalars behind `s_digits`, kept for the Phase 2h split
    /// path (zero for invalid lanes, which are masked out downstream).
    s_scalars: [Scalar; SIMD_LANES],
    messages: [&'a [u8]; SIMD_LANES],
}

/// Batch Ed25519 verifier for a fixed [`VerifyPolicy`] and [`KeyCache`].
/// Reuse one across [`verify_batch`](Verifier::verify_batch) calls.
#[derive(Debug)]
pub struct Verifier<C: KeyCache = NullKeyCache> {
    policy: VerifyPolicy,
    base_table: &'static BasepointTable,
    base_table_hi: &'static BasepointTable,
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
            base_table_hi: &*BASE_TABLE_PRIME,
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
            s_scalars,
            messages,
        } = parse_chunk_inputs(inputs);
        if !any_lane(&valid) {
            return;
        }

        let cached_keys: [Option<&CachedPublicKey>; SIMD_LANES] =
            core::array::from_fn(|lane| self.cache.get(&public_keys[lane]));
        let missing_key_lanes: [bool; SIMD_LANES] =
            core::array::from_fn(|lane| cached_keys[lane].is_none());

        // Phase 2h split ladder: every lane is a hit whose entry carries the
        // promoted A′ table — run the halved-doubling ladder (both policies;
        // it computes the same group element). No misses means nothing to
        // decode, insert, or promote afterwards.
        if cached_keys
            .iter()
            .all(|key| key.is_some_and(|key| key.table_hi.is_some()))
        {
            self.verify_split_chunk(
                &cached_keys,
                &r_bytes,
                &public_keys,
                &s_scalars,
                messages,
                &valid,
                out,
            );
            return;
        }

        // Phase 2h lazy promotion with hysteresis: promote a key on its
        // SECOND hit since insert. Keys oscillating between hit and eviction
        // (capacity churn) never reach two hits, so churn never rebuilds A′
        // and stays at exact 1b cost. Recover base points now (cheap; the
        // cache borrow is live) — the SIMD pass runs after verification.
        let promote_lanes: [bool; SIMD_LANES] = core::array::from_fn(|lane| {
            cached_keys[lane].is_some_and(|key| key.table_hi.is_none() && key.hits.get() >= 2)
        });
        let promote_points: [EdwardsPoint; SIMD_LANES] = core::array::from_fn(|lane| {
            if promote_lanes[lane] {
                cached_keys[lane]
                    .expect("promote lane is a cache hit")
                    .table
                    .recover_base_point()
            } else {
                EdwardsPoint::identity()
            }
        });

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

        // The affine public-key ladder is valid only when every lane's table is
        // affine-normalized (all cache hits from a normalizing cache); a single
        // projective miss table forces the projective add for the whole chunk.
        let all_affine = public_key_tables.iter().all(|table| table.is_affine());

        let prepared = PreparedBatch {
            public_key_tables,
            s_digits: &s_digits,
            k_digits: &k_digits,
            all_affine,
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
                        // Lazy: a retaining cache promotes after repeat hits.
                        table_hi: None,
                        hits: core::cell::Cell::new(0),
                    });
                }
            }
        }

        // Phase 2h lazy promotion: one wide 127-doubling pass shared by every
        // promoting lane in the chunk, then hand the upgraded entries back
        // through the cache (which adopts table_hi; NullKeyCache drops it).
        // Once per key ever; the split ladder engages from the next chunk on.
        if any_lane(&promote_lanes) {
            let hi_tables = avx512ifma::build_promoted_split_tables(&promote_points);
            for (lane, hi_table) in hi_tables.into_iter().enumerate() {
                if !promote_lanes[lane] {
                    continue;
                }
                // Duplicate (padded) lanes may already have been promoted by
                // an earlier lane this loop; the adopt path ignores repeats.
                let Some(existing) = self.cache.get(&public_keys[lane]) else {
                    continue; // evicted mid-batch by an insert above
                };
                let upgraded = CachedPublicKey {
                    encoded: public_keys[lane],
                    // 1b-fix: the main table is normalized HERE, at promotion,
                    // not at insert — resident entries are projective until
                    // their second hit, so churn inserts pay nothing.
                    table: existing.table.normalized_affine(),
                    table_hi: Some(hi_table.normalized_affine()),
                    hits: existing.hits.clone(),
                };
                self.cache.insert(upgraded);
            }
        }
    }

    /// Phase 2h split-ladder chunk (design addendum §3/§5): all lanes are
    /// cache hits with promoted entries; k and s are integer-split at bit 127
    /// and the four 32-digit halves drive the 124-doubling ladder over
    /// (A, A′, B, B′). Computes exactly [s]B − [k]A, so the policy tails are
    /// verbatim mirrors of the all-hit paths below.
    #[allow(clippy::too_many_arguments)]
    fn verify_split_chunk(
        &self,
        cached_keys: &[Option<&CachedPublicKey>; SIMD_LANES],
        r_bytes: &[[u8; R_ENCODING_LEN]; SIMD_LANES],
        public_keys: &[[u8; batch::PUBLIC_KEY_LEN]; SIMD_LANES],
        s_scalars: &[Scalar; SIMD_LANES],
        messages: [&[u8]; SIMD_LANES],
        valid: &[bool; SIMD_LANES],
        out: &mut [bool; SIMD_LANES],
    ) {
        let entry = |lane: usize| cached_keys[lane].expect("split chunk lanes are hits");
        let a_tables: [&PointTable; SIMD_LANES] = core::array::from_fn(|lane| &entry(lane).table);
        let a_hi_tables: [&PointTable; SIMD_LANES] = core::array::from_fn(|lane| {
            entry(lane)
                .table_hi
                .as_ref()
                .expect("split chunk lanes carry table_hi")
        });

        let k_scalars = challenge_scalars(r_bytes, public_keys, messages);
        let mut k0_digits = [[0i8; 32]; SIMD_LANES];
        let mut k1_digits = [[0i8; 32]; SIMD_LANES];
        let mut s0_digits = [[0i8; 32]; SIMD_LANES];
        let mut s1_digits = [[0i8; 32]; SIMD_LANES];
        for lane in 0..SIMD_LANES {
            (k0_digits[lane], k1_digits[lane]) = k_scalars[lane].split_radix16();
            (s0_digits[lane], s1_digits[lane]) = s_scalars[lane].split_radix16();
        }

        let prepared = PreparedSplitBatch {
            a_tables,
            a_hi_tables,
            k0_digits: &k0_digits,
            k1_digits: &k1_digits,
            s0_digits: &s0_digits,
            s1_digits: &s1_digits,
        };
        match self.policy {
            VerifyPolicy::Zip215 => {
                let (simd, r_valid_lanes) = avx512ifma::verify_prepared_split_zip215(
                    &prepared,
                    r_bytes,
                    self.base_table,
                    self.base_table_hi,
                );
                for lane in 0..SIMD_LANES {
                    out[lane] = simd[lane] && valid[lane] && r_valid_lanes[lane];
                }
            }
            VerifyPolicy::Dalek => {
                // All-hit chunk: R was never decompressed, so recompute and
                // compare bytes — the same tail as verify_prepared_dalek.
                let simd = avx512ifma::verify_prepared_split_dalek(
                    &prepared,
                    r_bytes,
                    self.base_table,
                    self.base_table_hi,
                );
                for lane in 0..SIMD_LANES {
                    out[lane] = simd[lane]
                        && valid[lane]
                        && !dalek_legacy_excluded(&public_keys[lane], &r_bytes[lane]);
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
    let mut s_scalars = [Scalar::from_canonical_bytes([0u8; 32]); SIMD_LANES];
    let mut messages = [inputs[0].message; SIMD_LANES];
    for (lane, input) in inputs.iter().enumerate() {
        r_bytes[lane].copy_from_slice(&input.signature[..R_ENCODING_LEN]);

        let mut s_bytes = [0u8; 32];
        s_bytes.copy_from_slice(&input.signature[R_ENCODING_LEN..]);
        if scalar::is_canonical(&s_bytes) {
            let scalar = Scalar::from_canonical_bytes(s_bytes);
            s_digits[lane] = scalar.to_radix16();
            s_scalars[lane] = scalar;
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
        s_scalars,
        messages,
    }
}

#[inline(always)]
fn challenge_digits(
    r_bytes: &[[u8; R_ENCODING_LEN]; SIMD_LANES],
    public_keys: &[[u8; batch::PUBLIC_KEY_LEN]; SIMD_LANES],
    messages: [&[u8]; SIMD_LANES],
) -> [Radix16; SIMD_LANES] {
    let scalars = challenge_scalars(r_bytes, public_keys, messages);
    core::array::from_fn(|lane| scalars[lane].to_radix16())
}

/// The reduced challenge scalars k = SHA-512(R‖A‖M) mod ℓ, shared by the
/// full-ladder digit path and the Phase 2h split path.
#[inline(always)]
fn challenge_scalars(
    r_bytes: &[[u8; R_ENCODING_LEN]; SIMD_LANES],
    public_keys: &[[u8; batch::PUBLIC_KEY_LEN]; SIMD_LANES],
    messages: [&[u8]; SIMD_LANES],
) -> [Scalar; SIMD_LANES] {
    let digests = sha512::hash_ed25519_challenge_words(r_bytes, public_keys, messages);
    core::array::from_fn(|lane| Scalar::from_wide_words(digests[lane]))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{HotKeyCache, NullKeyCache};
    use curve25519::ed_sigs::{SigningKey, VerificationKeyBytes};

    struct Owned {
        pk: [u8; 32],
        sig: [u8; 64],
        msg: Vec<u8>,
    }

    fn signed_inputs(round: u8) -> Vec<Owned> {
        (0..8u64)
            .map(|i| {
                let mut seed = [0u8; 32];
                seed[..8].copy_from_slice(&i.to_le_bytes());
                let key = SigningKey::from(seed);
                let msg = vec![round, i as u8, 0x2b];
                Owned {
                    pk: <[u8; 32]>::from(VerificationKeyBytes::from(&key)),
                    sig: key.sign(&msg).to_bytes(),
                    msg,
                }
            })
            .collect()
    }

    fn inputs_of(cases: &[Owned]) -> Vec<VerifyInput<'_>> {
        cases
            .iter()
            .map(|c| VerifyInput {
                public_key: c.pk,
                signature: c.sig,
                message: &c.msg,
            })
            .collect()
    }

    /// Phase 2h end-to-end semantics, both policies:
    /// round 1 (all miss)   -> insert, no split tables (lazy);
    /// round 2 (hit #1)     -> full ladder, NO promotion (hysteresis);
    /// round 3 (hit #2)     -> full ladder, promotion after the chunk;
    /// round 4+ (promoted)  -> split ladder, including a corrupted lane
    ///                         exercising per-lane masking through it.
    /// Every round's outputs must equal a cold NullKeyCache verifier's.
    /// (Note: test-side `warm.cache().get()` calls also bump hit counters,
    /// so the promotion round here is an upper bound of the production
    /// timeline — the invariants checked are lazy-insert, hysteresis ≥ one
    /// full-ladder reuse round, eventual promotion, and split correctness.)
    #[test]
    fn split_path_promotes_lazily_and_matches_cold_verifier() {
        for policy in [VerifyPolicy::Zip215, VerifyPolicy::Dalek] {
            let mut warm = Verifier::with_cache(policy, HotKeyCache::new());
            let mut cold = Verifier::with_cache(policy, NullKeyCache::new());

            let count_promoted = |warm: &Verifier<HotKeyCache>, cases: &[Owned]| {
                cases
                    .iter()
                    .filter(|c| {
                        warm.cache()
                            .get(&c.pk)
                            .is_some_and(|k| k.table_hi.as_ref().is_some_and(|t| t.is_affine()))
                    })
                    .count()
            };

            for round in 1u8..=5 {
                let mut cases = signed_inputs(round);
                if round >= 4 {
                    // Corrupt one signature: the split chunk must mask it out.
                    cases[3].sig[10] ^= 0x40;
                }
                let inputs = inputs_of(&cases);
                let mut got = vec![false; inputs.len()];
                let mut expect = vec![false; inputs.len()];
                warm.verify_batch(&inputs, &mut got);
                cold.verify_batch(&inputs, &mut expect);
                assert_eq!(got, expect, "warm/cold divergence in round {round} ({policy:?})");
                if round >= 4 {
                    assert!(!got[3] && got.iter().filter(|&&b| b).count() == 7);
                } else {
                    assert!(got.iter().all(|&b| b), "all-valid round {round}");
                }

                match round {
                    1 => {
                        assert_eq!(
                            count_promoted(&warm, &cases),
                            0,
                            "insert must not promote (lazy)"
                        );
                        // 1b-fix: freshly inserted entries stay as decoded.
                        assert!(
                            cases.iter().all(|c| warm
                                .cache()
                                .get(&c.pk)
                                .is_some_and(|k| !k.table.is_affine())),
                            "insert must not normalize (lazy 1b)"
                        );
                    }
                    // Rounds 2..3: hysteresis in effect; counting via get()
                    // perturbs hit counters, so only assert the endpoint:
                    3.. => assert_eq!(
                        count_promoted(&warm, &cases),
                        8,
                        "keys with repeat hits must be promoted by round {round}"
                    ),
                    _ => {}
                }
            }
        }
    }
}
