use super::{R_ENCODING_LEN, SIMD_LANES, VerificationPolicy, Verifier, VerifyPolicy};
use crate::batch::{self, PendingLanes};
use crate::edwards::PointTable;
use crate::input::{PUBLIC_KEY_LEN, VerifyInput};
use crate::scalar::{Radix16, prepare_signature_scalars};
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

impl<P: VerificationPolicy> Verifier<P> {
    /// Verify a batch and write one boolean result per input. `out[i]` is
    /// `true` iff `inputs[i]`'s signature is valid for its `(public_key, message)`.
    ///
    /// # Panics
    ///
    /// Panics if `inputs.len() != out.len()`.
    pub fn verify_batch(&mut self, inputs: &[VerifyInput<'_>], out: &mut [bool]) {
        assert_eq!(inputs.len(), out.len());
        batch::for_each_simd_chunk(inputs, &mut self.visit_order, |chunk, indices, active| {
            verify_chunk::<P>(
                chunk,
                *indices,
                active,
                out,
                &mut self.key_tables,
                self.identity_table,
            );
        });
    }
}

fn verify_chunk<P: VerificationPolicy>(
    inputs: &[VerifyInput<'_>; SIMD_LANES],
    output_indices: [usize; SIMD_LANES],
    active_lane_count: usize,
    out: &mut [bool],
    key_tables: &mut MaybeUninit<[PointTable; SIMD_LANES]>,
    identity_table: &PointTable,
) {
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
        lanes.reject(out);
        return;
    }

    let batch = avx512ifma::decode_keys_and_decompress_r(&public_keys, &r_bytes, key_tables);

    let public_key_tables: [&PointTable; SIMD_LANES] = core::array::from_fn(|lane| {
        if batch.valid[lane] {
            &batch.tables[lane]
        } else {
            lanes.valid[lane] = false;
            identity_table
        }
    });
    if P::POLICY == VerifyPolicy::Dalek {
        avx512ifma::reject_small_order_keys(&public_key_tables, &mut lanes.valid);
    }

    if any_lane(&lanes.valid) {
        let digests = sha512::hash_ed25519_challenge_words(&r_bytes, &public_keys, messages);
        let chunk = HashedChunk {
            public_key_tables,
            s_digits: &s_digits,
            digests: &digests,
        };
        avx512ifma::check_decoded::<P>(&chunk, &batch.r, batch.r_valid, &lanes, out);
    } else {
        lanes.reject(out);
    }
}

#[inline(always)]
fn parse_chunk_inputs<'a>(inputs: &[VerifyInput<'a>; SIMD_LANES]) -> ParsedChunk<'a> {
    let (mask, s_digits) = prepare_signature_scalars(
        inputs
            .each_ref()
            .map(|input| input.signature[R_ENCODING_LEN..].try_into().unwrap()),
    );
    ParsedChunk {
        valid: batch::mask_to_lanes(mask),
        r_bytes: inputs
            .each_ref()
            .map(|input| *input.signature.first_chunk().unwrap()),
        public_keys: inputs.each_ref().map(|input| input.public_key),
        s_digits,
        messages: inputs.each_ref().map(|input| input.message),
    }
}

fn any_lane(lanes: &[bool; SIMD_LANES]) -> bool {
    lanes.iter().any(|&lane| lane)
}
