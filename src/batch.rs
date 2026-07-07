use crate::edwards::PointTable;
use crate::scalar::Radix16;
use crate::verifier::VerifyInput;

/// Byte length of an encoded Ed25519 public key.
pub const PUBLIC_KEY_LEN: usize = 32;
/// Byte length of an encoded Ed25519 signature.
pub const SIGNATURE_LEN: usize = 64;
/// Byte length of a signature's compressed `R` point. Numerically the same as
/// `PUBLIC_KEY_LEN` (both are compressed Edwards points), but kept as a
/// separate constant since an `R` value is never a public key.
pub(crate) const R_ENCODING_LEN: usize = 32;
/// Number of verification lanes processed by one SIMD chunk.
pub(crate) const SIMD_LANES: usize = 8;

pub(crate) struct PreparedBatch<'a> {
    pub(crate) public_key_tables: [&'a PointTable; SIMD_LANES],
    pub(crate) s_digits: &'a [Radix16; SIMD_LANES],
    pub(crate) k_digits: &'a [Radix16; SIMD_LANES],
}

/// Visit inputs as padded SIMD chunks, grouping mixed message lengths by
/// SHA-512 block count so each SIMD challenge hash does less divergent work.
pub(crate) fn for_each_simd_chunk<'a>(
    inputs: &[VerifyInput<'a>],
    order: &mut Vec<usize>,
    visit: impl FnMut(&[VerifyInput<'a>; SIMD_LANES], &[usize; SIMD_LANES], usize),
) {
    if should_bucket_by_block_count(inputs) {
        for_each_bucketed_simd_chunk(inputs, order, visit);
    } else {
        for_each_in_order_simd_chunk(inputs, visit);
    }
}

/// Visit already-contiguous chunks and pad the tail with a duplicate lane.
fn for_each_in_order_simd_chunk<'a>(
    inputs: &[VerifyInput<'a>],
    mut visit: impl FnMut(&[VerifyInput<'a>; SIMD_LANES], &[usize; SIMD_LANES], usize),
) {
    // Process full SIMD-width chunks directly before padding any tail lanes.
    let (chunks, _) = inputs.as_chunks::<SIMD_LANES>();
    for (chunk_index, chunk) in chunks.iter().enumerate() {
        let output_indices = core::array::from_fn(|lane| chunk_index * SIMD_LANES + lane);
        visit(chunk, &output_indices, SIMD_LANES);
    }

    // Pad and process any trailing partial chunk for the fixed-width SIMD visitor.
    let i = chunks.len() * SIMD_LANES;
    let rem = inputs.len() - i;
    if rem > 0 {
        let mut chunk = [inputs[inputs.len() - 1]; SIMD_LANES];
        chunk[..rem].copy_from_slice(&inputs[i..]);
        let output_indices = core::array::from_fn(|lane| i + lane);
        visit(&chunk, &output_indices, rem);
    }
}

/// Visit chunks in block-count bucket order while reporting original indices.
fn for_each_bucketed_simd_chunk<'a>(
    inputs: &[VerifyInput<'a>],
    order: &mut Vec<usize>,
    mut visit: impl FnMut(&[VerifyInput<'a>; SIMD_LANES], &[usize; SIMD_LANES], usize),
) {
    sort_indices_by_block_count(inputs, order);

    // Process full SIMD-width chunks in bucketed order while preserving original output indices.
    let mut i = 0;
    while i + SIMD_LANES <= order.len() {
        let output_indices: [usize; SIMD_LANES] = core::array::from_fn(|lane| order[i + lane]);
        let chunk: [VerifyInput<'a>; SIMD_LANES] =
            core::array::from_fn(|lane| inputs[output_indices[lane]]);
        visit(&chunk, &output_indices, SIMD_LANES);
        i += SIMD_LANES;
    }

    // Pad the trailing bucketed inputs with the last index for the fixed-width SIMD visitor.
    let rem = order.len() - i;
    if rem > 0 {
        let last = order[order.len() - 1];
        let output_indices: [usize; SIMD_LANES] =
            core::array::from_fn(|lane| if lane < rem { order[i + lane] } else { last });
        let chunk: [VerifyInput<'a>; SIMD_LANES] =
            core::array::from_fn(|lane| inputs[output_indices[lane]]);
        visit(&chunk, &output_indices, rem);
    }
}

/// Bucket only when enough inputs have mixed SHA-512 challenge block counts.
fn should_bucket_by_block_count(inputs: &[VerifyInput<'_>]) -> bool {
    if inputs.len() < SIMD_LANES * 2 {
        return false;
    }

    // Check if all messages have the same block count.
    let first = challenge_block_count(inputs[0].message.len());
    let mut i = 1;
    while i < inputs.len() {
        if challenge_block_count(inputs[i].message.len()) != first {
            return true;
        }
        i += 1;
    }
    false
}

/// Group original input indices by challenge block count; bucket order itself
/// is irrelevant.
fn sort_indices_by_block_count(inputs: &[VerifyInput<'_>], order: &mut Vec<usize>) {
    order.clear();
    order.extend(0..inputs.len());
    order.sort_unstable_by_key(|&i| challenge_block_count(inputs[i].message.len()));
}

/// SHA-512 block count for `R || A || M`, including padding and length trailer.
/// Must stay in sync with the SIMD hasher.
#[inline]
pub(crate) fn challenge_block_count(message_len: usize) -> usize {
    message_len.saturating_add(64 + 1 + 16).div_ceil(128)
}
