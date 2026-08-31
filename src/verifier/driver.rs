use super::policy::{
    PendingLanes, PolicyOps, ScoredLanes, UncachedPolicyOps, score_dalek_lanes, score_zip215_lanes,
};
use super::{R_ENCODING_LEN, SIMD_LANES, VerificationPolicy, Verifier};
use crate::batch;
use crate::cache::{CachedPublicKey, KeyCache, NullKeyCache};
use crate::edwards::PointTable;
use crate::hot_key_cache::HotKeyCache;
use crate::input::{PUBLIC_KEY_LEN, VerifyInput};
use crate::scalar::{self, Radix16, Scalar};
use crate::sha512;
use crate::wide::{PreparedChunk, avx512ifma};

struct ParsedChunk<'a> {
    valid: [bool; SIMD_LANES],
    r_bytes: [[u8; R_ENCODING_LEN]; SIMD_LANES],
    public_keys: [[u8; PUBLIC_KEY_LEN]; SIMD_LANES],
    s_digits: [Radix16; SIMD_LANES],
    messages: [&'a [u8]; SIMD_LANES],
}

#[derive(Debug)]
pub(super) struct ChunkScratch {
    key_tables: [Option<PointTable>; SIMD_LANES],
}

impl ChunkScratch {
    pub(super) fn new() -> Self {
        Self {
            key_tables: core::array::from_fn(|_| None),
        }
    }
}

impl<P: VerificationPolicy, C: KeyCache> Verifier<P, C> {
    /// Verify one chunk, returning whether its policy-specific result was
    /// queued for shared inversion work instead of scored here. Queuing writes straight into
    /// the caller's buffers: returning the candidate by value would put a
    /// kilobyte of `sret` traffic on every chunk, including the paths that
    /// never defer.
    fn verify_chunk(
        &mut self,
        inputs: &[VerifyInput<'_>; SIMD_LANES],
        output_indices: [usize; SIMD_LANES],
        active_lane_count: usize,
        out: &mut [bool; SIMD_LANES],
        queues: &mut P::Queues,
    ) -> bool
    where
        P: PolicyOps,
    {
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
            let (key_valid_bits, r_points, r_valid_bits) =
                P::decode_keys_and_r(&public_keys, &r_bytes, &mut self.scratch.key_tables);
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
            deferred = P::verify_lanes(self, &prepared, decoded_r, &lanes, out, queues);
            if deferred {
                P::push_pending(
                    queues,
                    PendingLanes {
                        valid,
                        output_indices,
                        active_lane_count,
                    },
                    r_bytes,
                    public_keys,
                );
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
        public_keys: &[[u8; PUBLIC_KEY_LEN]; SIMD_LANES],
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

    /// Score the lanes against an already-decompressed `R`, or queue the
    /// ladder result when `R` is still encoded so its decompression can pair
    /// with another chunk's. Returns whether the chunk was queued.
    #[inline(always)]
    pub(super) fn verify_zip215_lanes(
        &self,
        prepared: &PreparedChunk<'_>,
        decoded_r: Option<(avx512ifma::WideRPoint, [bool; SIMD_LANES])>,
        lanes: &ScoredLanes<'_>,
        out: &mut [bool; SIMD_LANES],
        zip_candidates: &mut Vec<avx512ifma::Zip215Candidate>,
    ) -> bool {
        // Cache misses already decompressed R alongside their keys.
        let Some((r_points, r_valid_lanes)) = decoded_r else {
            // Every lane hit the cache, so nothing decompressed `R`. Queue the
            // ladder result to share an interleaved decompression pair.
            zip_candidates.push(avx512ifma::prepare_zip215_candidate(
                prepared,
                self.base_table,
            ));
            return true;
        };

        let equation_holds =
            avx512ifma::verify_prepared_zip215(prepared, &r_points, self.base_table);
        score_zip215_lanes(&equation_holds, &r_valid_lanes, lanes, out);
        false
    }

    /// Score the lanes against an already-decompressed `R`, or queue the point
    /// when `R` is still encoded so the recompression can share an inversion.
    /// Returns whether the chunk was queued.
    #[inline(always)]
    pub(super) fn verify_dalek_lanes(
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
        score_dalek_lanes(&equation_holds, &r_points, &r_valid_lanes, lanes, out);
        false
    }
}

impl<P: VerificationPolicy> Verifier<P, NullKeyCache> {
    /// Verify one chunk on the configuration where every cache lookup is
    /// statically known to miss.
    fn verify_uncached_chunk(
        &mut self,
        inputs: &[VerifyInput<'_>; SIMD_LANES],
        out: &mut [bool; SIMD_LANES],
    ) where
        P: UncachedPolicyOps,
    {
        let ParsedChunk {
            mut valid,
            r_bytes,
            public_keys,
            s_digits,
            messages,
        } = parse_chunk_inputs(inputs);
        if !any_lane(&valid) {
            return;
        }

        let (key_valid_bits, r_points, r_valid_bits) =
            P::decode_keys_and_r(&public_keys, &r_bytes, &mut self.scratch.key_tables);
        let decoded_key_lanes = avx512ifma::mask_to_lanes(key_valid_bits);
        let r_valid_lanes = avx512ifma::mask_to_lanes(r_valid_bits);

        let public_key_tables: [&PointTable; SIMD_LANES] = core::array::from_fn(|lane| {
            if decoded_key_lanes[lane] {
                self.scratch.key_tables[lane]
                    .as_ref()
                    .expect("a valid decoded lane has a table")
            } else {
                valid[lane] = false;
                self.identity_table
            }
        });

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
            P::verify_decoded_lanes(self, &prepared, &r_points, &r_valid_lanes, &lanes, out);
        }

        // Decoding fills every scratch slot. NullKeyCache retains none of them.
        for table in &mut self.scratch.key_tables {
            let _ = table.take().expect("a decode fills every lane's slot");
        }
    }
}

pub(super) fn verify_cached_batch_for<P: PolicyOps>(
    verifier: &mut Verifier<P, HotKeyCache>,
    inputs: &[VerifyInput<'_>],
    out: &mut [bool],
) {
    assert_eq!(inputs.len(), out.len());
    let mut visit_order = core::mem::take(&mut verifier.visit_order);
    let mut queues = core::mem::take(&mut verifier.queues);
    batch::for_each_simd_chunk(
        inputs,
        &mut visit_order,
        |chunk, output_indices, active_lane_count| {
            let mut tmp = [false; SIMD_LANES];
            let deferred = verifier.verify_chunk(
                chunk,
                *output_indices,
                active_lane_count,
                &mut tmp,
                &mut queues,
            );
            if !deferred {
                for (&index, &value) in output_indices[..active_lane_count].iter().zip(&tmp) {
                    out[index] = value;
                }
            } else if P::queue_is_full(&queues) {
                P::flush_queue(&mut queues, out);
            }
        },
    );
    P::flush_queue(&mut queues, out);
    verifier.visit_order = visit_order;
    verifier.queues = queues;
}

pub(super) fn verify_uncached_batch_for<P: UncachedPolicyOps>(
    verifier: &mut Verifier<P, NullKeyCache>,
    inputs: &[VerifyInput<'_>],
    out: &mut [bool],
) {
    assert_eq!(inputs.len(), out.len());
    let mut visit_order = core::mem::take(&mut verifier.visit_order);
    batch::for_each_simd_chunk(
        inputs,
        &mut visit_order,
        |chunk, output_indices, active_lane_count| {
            let mut tmp = [false; SIMD_LANES];
            verifier.verify_uncached_chunk(chunk, &mut tmp);
            for (&index, &value) in output_indices[..active_lane_count].iter().zip(&tmp) {
                out[index] = value;
            }
        },
    );
    verifier.visit_order = visit_order;
}

#[inline(always)]
fn parse_chunk_inputs<'a>(inputs: &[VerifyInput<'a>; SIMD_LANES]) -> ParsedChunk<'a> {
    let mut valid = [true; SIMD_LANES];
    let mut r_bytes = [[0u8; R_ENCODING_LEN]; SIMD_LANES];
    let mut public_keys = [[0u8; PUBLIC_KEY_LEN]; SIMD_LANES];
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
    public_keys: &[[u8; PUBLIC_KEY_LEN]; SIMD_LANES],
    messages: [&[u8]; SIMD_LANES],
) -> [Radix16; SIMD_LANES] {
    let digests = sha512::hash_ed25519_challenge_words(r_bytes, public_keys, messages);
    scalar::wide_words_to_radix16(&digests)
}

fn any_lane(lanes: &[bool; SIMD_LANES]) -> bool {
    lanes.iter().any(|&lane| lane)
}
