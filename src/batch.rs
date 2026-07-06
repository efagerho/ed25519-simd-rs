use crate::edwards::PointTable;
use crate::scalar::Radix16;
use crate::verifier::VerifyInput;

/// Byte length of an encoded Ed25519 public key.
pub const PUBLIC_KEY_LEN: usize = 32;
/// Byte length of an encoded Ed25519 signature.
pub const SIGNATURE_LEN: usize = 64;
/// Number of verification lanes processed by one SIMD chunk.
pub(crate) const SIMD_LANES: usize = 8;
const BUCKET_HISTOGRAM_BLOCKS: usize = 64;

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
    let (chunks, _) = inputs.as_chunks::<SIMD_LANES>();
    for (chunk_index, chunk) in chunks.iter().enumerate() {
        let output_indices = core::array::from_fn(|lane| chunk_index * SIMD_LANES + lane);
        visit(chunk, &output_indices, SIMD_LANES);
    }

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
    build_block_bucket_order(inputs, order);

    let mut i = 0;
    while i + SIMD_LANES <= order.len() {
        let mut chunk = [inputs[order[i]]; SIMD_LANES];
        let mut output_indices = [0usize; SIMD_LANES];
        let mut lane = 0;
        while lane < SIMD_LANES {
            let index = order[i + lane];
            chunk[lane] = inputs[index];
            output_indices[lane] = index;
            lane += 1;
        }
        visit(&chunk, &output_indices, SIMD_LANES);
        i += SIMD_LANES;
    }

    let rem = order.len() - i;
    if rem > 0 {
        let last = order[order.len() - 1];
        let mut chunk = [inputs[last]; SIMD_LANES];
        let mut output_indices = [0usize; SIMD_LANES];
        let mut lane = 0;
        while lane < rem {
            let index = order[i + lane];
            chunk[lane] = inputs[index];
            output_indices[lane] = index;
            lane += 1;
        }
        visit(&chunk, &output_indices, rem);
    }
}

/// Bucket only when enough inputs have mixed SHA-512 challenge block counts.
fn should_bucket_by_block_count(inputs: &[VerifyInput<'_>]) -> bool {
    if inputs.len() < SIMD_LANES * 2 {
        return false;
    }

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

/// Build original input indices sorted by challenge block count.
fn build_block_bucket_order(inputs: &[VerifyInput<'_>], order: &mut Vec<usize>) {
    let mut max_block_count = 0usize;
    let mut i = 0;
    while i < inputs.len() {
        max_block_count = max_block_count.max(challenge_block_count(inputs[i].message.len()));
        i += 1;
    }

    order.clear();
    if max_block_count > BUCKET_HISTOGRAM_BLOCKS {
        build_sparse_block_bucket_order(inputs, order);
        return;
    }

    let mut counts = [0usize; BUCKET_HISTOGRAM_BLOCKS + 1];
    i = 0;
    while i < inputs.len() {
        counts[challenge_block_count(inputs[i].message.len())] += 1;
        i += 1;
    }

    let mut next = [0usize; BUCKET_HISTOGRAM_BLOCKS + 1];
    let mut total = 0usize;
    i = 0;
    while i < counts.len() {
        next[i] = total;
        total += counts[i];
        i += 1;
    }

    order.resize(inputs.len(), 0);
    i = 0;
    while i < inputs.len() {
        let block_count = challenge_block_count(inputs[i].message.len());
        let pos = next[block_count];
        next[block_count] += 1;
        order[pos] = i;
        i += 1;
    }
}

/// Build bucket order without a dense count table for very long messages.
/// Only grouping same-block-count inputs together matters (see
/// `for_each_bucketed_simd_chunk`), not the order buckets appear in, so a
/// direct sort by block count suffices — no hash table needed.
fn build_sparse_block_bucket_order(inputs: &[VerifyInput<'_>], order: &mut Vec<usize>) {
    order.extend(0..inputs.len());
    order.sort_unstable_by_key(|&i| challenge_block_count(inputs[i].message.len()));
}

/// Number of SHA-512 blocks needed to hash the `R || A || M` Ed25519
/// challenge preimage for a message of `message_len` bytes (`R` and `A` are
/// 32 bytes each, `64`; `+ 1 + 16` accounts for the `0x80` padding byte and
/// the 16-byte big-endian bit-length trailer). Shared with `sha512.rs`, which
/// must bucket and hash messages using the exact same block count.
#[inline]
pub(crate) fn challenge_block_count(message_len: usize) -> usize {
    message_len.saturating_add(64 + 1 + 16).div_ceil(128)
}
