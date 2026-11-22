use super::policy::PolicyOps;
use super::{R_ENCODING_LEN, SIMD_LANES, VerificationPolicy, Verifier};
use crate::batch::{self, PendingLanes};
use crate::cache::{CachedPublicKey, KeyCache, NullKeyCache};
use crate::edwards::PointTable;
use crate::hot_key_cache::HotKeyCache;
use crate::input::{PUBLIC_KEY_LEN, VerifyInput};
use crate::scalar::{self, CanonicalScalar, Radix16};
use crate::sha512;
use crate::wide::{HashedChunk, avx512ifma};
use core::mem::MaybeUninit;

/// One input chunk parsed into the structure-of-arrays layout used by SIMD code.
///
/// Eight `R` encodings become one contiguous lane array that a
/// decompression pass loads into vector field elements.
struct ParsedChunk<'a> {
    valid: [bool; SIMD_LANES],
    r_bytes: [[u8; R_ENCODING_LEN]; SIMD_LANES],
    public_keys: [[u8; PUBLIC_KEY_LEN]; SIMD_LANES],
    s_digits: [Radix16; SIMD_LANES],
    messages: [&'a [u8]; SIMD_LANES],
}

/// Reusable point-table storage for public keys decoded during verification.
///
/// Each chunk overwrites these eight slots instead of allocating
/// a fresh table array before its multiscalar ladder.
#[derive(Debug)]
pub(super) struct ChunkScratch {
    key_tables: MaybeUninit<[PointTable; SIMD_LANES]>,
}

impl ChunkScratch {
    pub(super) fn new() -> Self {
        Self {
            key_tables: MaybeUninit::uninit(),
        }
    }
}

impl<P: VerificationPolicy, C: KeyCache> Verifier<P, C> {
    fn verify_chunk(
        &mut self,
        inputs: &[VerifyInput<'_>; SIMD_LANES],
        output_indices: [usize; SIMD_LANES],
        active_lane_count: usize,
        out: &mut [bool],
        queues: &mut P::Queues,
    ) where
        P: PolicyOps,
    {
        let ParsedChunk {
            valid,
            r_bytes,
            public_keys,
            s_digits,
            messages,
        } = parse_chunk_inputs(inputs);
        let mut lanes = PendingLanes {
            valid,
            output_indices,
            active_lane_count,
        };
        if !any_lane(&lanes.valid) {
            lanes.score(out, |_| false);
            return;
        }

        let cached_keys: [Option<&CachedPublicKey>; SIMD_LANES] =
            core::array::from_fn(|lane| self.cache.get(&public_keys[lane]));
        let missing_key_lanes: [bool; SIMD_LANES] =
            core::array::from_fn(|lane| cached_keys[lane].is_none());

        // Decode missing keys and their R points together.
        let decoded = any_lane(&missing_key_lanes).then(|| {
            avx512ifma::decode_keys_and_decompress_r(
                &public_keys,
                &r_bytes,
                &mut self.scratch.key_tables,
            )
        });
        let public_key_tables: [&PointTable; SIMD_LANES] = core::array::from_fn(|lane| {
            if let Some(key) = cached_keys[lane] {
                &key.table
            } else if let Some(batch) = decoded.as_ref().filter(|batch| batch.valid[lane]) {
                &batch.tables[lane]
            } else {
                lanes.valid[lane] = false;
                self.identity_table
            }
        });
        P::reject_small_order_keys(&public_key_tables, &mut lanes.valid);

        // Skip the ladder, but still retain the keys that did decode.
        if any_lane(&lanes.valid) {
            let digests = sha512::hash_ed25519_challenge_words(&r_bytes, &public_keys, messages);
            let chunk = HashedChunk {
                public_key_tables,
                s_digits: &s_digits,
                digests: &digests,
                r_bytes: &r_bytes,
            };
            match &decoded {
                Some(batch) => P::verify_decoded(&chunk, &batch.r, batch.r_valid, &lanes, out),
                None => P::verify_encoded(&chunk, lanes, queues, out),
            }
        } else {
            lanes.score(out, |_| false);
        }
        if let Some(batch) = decoded {
            for lane in 0..SIMD_LANES {
                if missing_key_lanes[lane] && batch.valid[lane] {
                    self.cache.insert(CachedPublicKey {
                        encoded: public_keys[lane],
                        table: batch.tables[lane].clone(),
                    });
                }
            }
        }
    }
}

impl<P: VerificationPolicy> Verifier<P, NullKeyCache> {
    /// Verify one chunk on the configuration where every cache lookup is
    /// statically known to miss.
    fn verify_uncached_chunk(
        &mut self,
        inputs: &[VerifyInput<'_>; SIMD_LANES],
        output_indices: [usize; SIMD_LANES],
        active_lane_count: usize,
        out: &mut [bool],
    ) where
        P: PolicyOps,
    {
        let ParsedChunk {
            valid,
            r_bytes,
            public_keys,
            s_digits,
            messages,
        } = parse_chunk_inputs(inputs);
        let mut lanes = PendingLanes {
            valid,
            output_indices,
            active_lane_count,
        };
        if !any_lane(&lanes.valid) {
            lanes.score(out, |_| false);
            return;
        }

        let batch = avx512ifma::decode_keys_and_decompress_r(
            &public_keys,
            &r_bytes,
            &mut self.scratch.key_tables,
        );

        let public_key_tables: [&PointTable; SIMD_LANES] = core::array::from_fn(|lane| {
            if batch.valid[lane] {
                &batch.tables[lane]
            } else {
                lanes.valid[lane] = false;
                self.identity_table
            }
        });
        P::reject_small_order_keys(&public_key_tables, &mut lanes.valid);

        if any_lane(&lanes.valid) {
            let digests = sha512::hash_ed25519_challenge_words(&r_bytes, &public_keys, messages);
            let chunk = HashedChunk {
                public_key_tables,
                s_digits: &s_digits,
                digests: &digests,
                r_bytes: &r_bytes,
            };
            P::verify_decoded(&chunk, &batch.r, batch.r_valid, &lanes, out);
        } else {
            lanes.score(out, |_| false);
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
            verifier.verify_chunk(chunk, *output_indices, active_lane_count, out, &mut queues);
        },
    );
    P::flush_queue(&mut queues, out);
    verifier.visit_order = visit_order;
    verifier.queues = queues;
}

pub(super) fn verify_uncached_batch_for<P: PolicyOps>(
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
            verifier.verify_uncached_chunk(chunk, *output_indices, active_lane_count, out);
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
            s_digits[lane] = CanonicalScalar::from_canonical_bytes(s_bytes).to_radix16();
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

fn any_lane(lanes: &[bool; SIMD_LANES]) -> bool {
    lanes.iter().any(|&lane| lane)
}
