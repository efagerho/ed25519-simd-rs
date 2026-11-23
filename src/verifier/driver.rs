use super::{VerificationPolicy, Verifier};
use crate::batch::{self, PendingLanes};
use crate::input::VerifyInput;
use crate::sha512;
use crate::wide::avx512ifma;

impl<P: VerificationPolicy> Verifier<P> {
    /// Verify a batch and write one boolean result per input. `out[i]` is
    /// `true` iff `inputs[i]`'s signature is valid for its `(public_key, message)`.
    ///
    /// # Panics
    ///
    /// Panics if `inputs.len() != out.len()`.
    pub fn verify_batch(&mut self, inputs: &[VerifyInput<'_>], out: &mut [bool]) {
        assert_eq!(inputs.len(), out.len());
        batch::for_each_simd_chunk(inputs, &mut self.visit_order, |inputs, indices, active| {
            let Some((chunk, prepared)) = avx512ifma::prepare_chunk::<P>(inputs, &mut self.scratch)
            else {
                for &index in &indices[..active] {
                    out[index] = false;
                }
                return;
            };
            let lanes = PendingLanes {
                valid: prepared.valid,
                output_indices: *indices,
                active_lane_count: active,
            };
            let digests = sha512::hash_ed25519_challenge_words(
                &chunk.r_bytes,
                &chunk.public_keys,
                inputs.each_ref().map(|input| input.message),
            );
            avx512ifma::check_decoded::<P>(chunk, &prepared, &digests, &lanes, out);
        });
    }
}
