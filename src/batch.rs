use crate::input::VerifyInput;

/// Number of verification lanes processed by one SIMD chunk.
pub(crate) const SIMD_LANES: usize = 8;

/// One input to the native batch driver. All five fields are individual
/// machine words. The message pointer and length come from the same slice.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct BatchInput<'a> {
    key: &'a [u8; 32],
    signature: &'a [u8; 64],
    message: *const u8,
    message_len: usize,
    output_index: usize,
}

const _: () = {
    use core::mem::{offset_of, size_of};
    assert!(size_of::<BatchInput>() == 40 && offset_of!(BatchInput, key) == 0);
    assert!(offset_of!(BatchInput, signature) == 8 && offset_of!(BatchInput, message) == 16);
    assert!(
        offset_of!(BatchInput, message_len) == 24 && offset_of!(BatchInput, output_index) == 32
    );
};

/// Borrow the inputs for one native call, sorting large mixed batches by
/// SHA-512 block count. A single SIMD chunk fits on the stack.
pub(crate) fn with_batch_inputs<T>(
    inputs: &[VerifyInput<'_>],
    run: impl FnOnce(&[BatchInput<'_>]) -> T,
) -> T {
    let mut rows = inputs
        .iter()
        .enumerate()
        .map(|(output_index, input)| BatchInput {
            key: &input.public_key,
            signature: &input.signature,
            message: input.message.as_ptr(),
            message_len: input.message.len(),
            output_index,
        });
    if inputs.len() <= SIMD_LANES {
        let Some(first) = rows.next() else {
            return run(&[]);
        };
        let mut inline = [first; SIMD_LANES];
        for (slot, row) in inline[1..].iter_mut().zip(rows) {
            *slot = row;
        }
        return run(&inline[..inputs.len()]);
    }

    let mut rows: Vec<_> = rows.collect();
    if rows.len() >= 2 * SIMD_LANES {
        let blocks = |row: &BatchInput<'_>| challenge_block_count(row.message_len);
        let first = blocks(&rows[0]);
        if rows[1..].iter().any(|row| blocks(row) != first) {
            rows.sort_unstable_by_key(blocks);
        }
    }
    run(&rows)
}

/// SHA-512 block count for `R || A || M`, including padding and length trailer.
/// Must stay in sync with the SIMD hasher.
#[inline]
pub(crate) fn challenge_block_count(message_len: usize) -> usize {
    message_len.saturating_add(64 + 1 + 16).div_ceil(128)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn inputs(count: usize, message: &[u8]) -> Vec<VerifyInput<'_>> {
        (0..count)
            .map(|i| VerifyInput {
                public_key: [i as u8; 32],
                signature: [i as u8; 64],
                message,
            })
            .collect()
    }

    #[test]
    fn scheduling_preserves_indices_and_groups_large_mixed_batches() {
        let long = [0u8; 200];
        for count in 0..=3 * SIMD_LANES + 1 {
            let mut inputs = inputs(count, b"short");
            for input in inputs.iter_mut().step_by(2) {
                input.message = &long;
            }
            with_batch_inputs(&inputs, |rows| {
                let indices: Vec<_> = rows.iter().map(|row| row.output_index).collect();
                if count < 2 * SIMD_LANES {
                    assert!(indices.iter().copied().eq(0..count));
                } else {
                    assert!(
                        rows.windows(2)
                            .all(|pair| pair[0].message_len <= pair[1].message_len)
                    );
                }
                let mut sorted = indices;
                sorted.sort_unstable();
                assert!(sorted.into_iter().eq(0..count));
                for row in rows {
                    let input = &inputs[row.output_index];
                    assert!(core::ptr::eq(row.key, &input.public_key));
                    assert!(core::ptr::eq(row.signature, &input.signature));
                    assert_eq!(row.message, input.message.as_ptr());
                    assert_eq!(row.message_len, input.message.len());
                }
            });
        }
    }

    #[test]
    fn challenge_block_count_matches_sha512_padding_boundaries() {
        // `R || A || M` is 64 bytes of prefix plus a 17-byte padding trailer.
        assert_eq!(challenge_block_count(0), 1);
        assert_eq!(challenge_block_count(47), 1);
        assert_eq!(challenge_block_count(48), 2);
        assert_eq!(challenge_block_count(175), 2);
        assert_eq!(challenge_block_count(176), 3);
        assert_eq!(challenge_block_count(usize::MAX), usize::MAX / 128 + 1);
    }
}
