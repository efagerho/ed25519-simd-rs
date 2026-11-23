use super::{VerificationPolicy, Verifier, VerifyPolicy};
use crate::batch::{BatchInput, with_batch_inputs};
use crate::edwards::{BASEPOINT_TABLE, BasepointTableEntries, IDENTITY_TABLE, PointTable};
use crate::input::VerifyInput;
use crate::wide::avx512ifma::ChunkScratch;

unsafe extern "C" {
    fn ed25519_simd_zip215_verify_batch(
        rows: *const BatchInput<'_>,
        count: usize,
        out: *mut bool,
        scratch: *mut ChunkScratch,
        identity: &PointTable,
        base: &BasepointTableEntries,
    ) -> u32;
    fn ed25519_simd_dalek_verify_batch(
        rows: *const BatchInput<'_>,
        count: usize,
        out: *mut bool,
        scratch: *mut ChunkScratch,
        identity: &PointTable,
        base: &BasepointTableEntries,
    ) -> u32;
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
        let verify = match P::POLICY {
            VerifyPolicy::Zip215 => ed25519_simd_zip215_verify_batch,
            VerifyPolicy::Dalek => ed25519_simd_dalek_verify_batch,
        };
        let ok = with_batch_inputs(inputs, |rows| {
            // SAFETY: every row borrows a live input and names one distinct
            // output position. Scratch is aligned, exclusive and disjoint
            // from the inputs and output. The callee writes only bool bytes.
            unsafe {
                verify(
                    rows.as_ptr(),
                    rows.len(),
                    out.as_mut_ptr(),
                    self.scratch.as_mut_ptr(),
                    &IDENTITY_TABLE,
                    &BASEPOINT_TABLE,
                )
            }
        });
        assert_eq!(ok, 1, "invalid verification output positions");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::GuardedPage;
    use curve25519::ed_sigs::{SigningKey, VerificationKeyBytes};

    #[test]
    fn native_batch_respects_record_and_output_extents() {
        let key = SigningKey::from([17; 32]);
        let message = b"batch entry";
        let signed = VerifyInput {
            public_key: VerificationKeyBytes::from(&key).into(),
            signature: key.sign(message).to_bytes(),
            message,
        };
        let inputs: [VerifyInput; 17] = core::array::from_fn(|i| {
            let mut input = signed;
            if (8..16).contains(&i) || i % 3 == 0 {
                input.signature[32..].fill(0xff);
            }
            input
        });
        let mut scratch = Box::<ChunkScratch>::new_uninit();

        for count in 0..=inputs.len() {
            with_batch_inputs(&inputs[..count], |rows| {
                for end in [false, true] {
                    let records = GuardedPage::new();
                    let output = GuardedPage::new();
                    let src = records.buffer(size_of_val(rows), end).cast::<BatchInput>();
                    let dst = output.buffer(count, end);
                    // Reverse the records so scoring must respect each original index.
                    for (i, row) in rows.iter().rev().enumerate() {
                        unsafe { src.add(i).write(*row) };
                    }
                    records.read_only();
                    for verify in [
                        ed25519_simd_zip215_verify_batch,
                        ed25519_simd_dalek_verify_batch,
                    ] {
                        let mut call = |len, out: *mut u8| unsafe {
                            verify(
                                src,
                                len,
                                out.cast(),
                                scratch.as_mut_ptr(),
                                &IDENTITY_TABLE,
                                &BASEPOINT_TABLE,
                            )
                        };
                        // At the upper boundary an empty call gets guard-page pointers.
                        unsafe { dst.write_bytes(0xa5, count) };
                        assert_eq!(call(count, dst), 1);
                        for (i, input) in inputs[..count].iter().enumerate() {
                            assert_eq!(
                                unsafe { dst.add(i).read() },
                                u8::from(input.signature == signed.signature)
                            );
                        }

                        // The first reversed record names count-1. With a single
                        // output byte it must fail both the decoded and rejection paths.
                        if count >= 2 {
                            let single = output.buffer(1, true);
                            unsafe { single.write(0xa5) };
                            assert_eq!(call(1, single), 0);
                            assert_eq!(unsafe { single.read() }, 0xa5);
                        }
                    }
                }
            });
        }
    }
}
