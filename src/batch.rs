use crate::input::VerifyInput;

/// Byte length of a signature's compressed `R` point.
pub(crate) const R_ENCODING_LEN: usize = crate::edwards::POINT_ENCODING_LEN;
/// Number of verification lanes processed by one SIMD chunk.
pub(crate) const SIMD_LANES: usize = 8;

/// Visit padded SIMD chunks, bucketed by SHA-512 block count when useful.
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
        let last = inputs.len() - 1;
        let mut chunk = [inputs[last]; SIMD_LANES];
        chunk[..rem].copy_from_slice(&inputs[i..]);
        // Padding lanes repeat the last index rather than running past the end.
        // Visitors only read `..rem`, but an in-range array cannot become an
        // out-of-bounds write if that ever changes.
        let output_indices = core::array::from_fn(|lane| if lane < rem { i + lane } else { last });
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

    let mut i = 0;
    while i + SIMD_LANES <= order.len() {
        let output_indices: [usize; SIMD_LANES] = core::array::from_fn(|lane| order[i + lane]);
        let chunk: [VerifyInput<'a>; SIMD_LANES] =
            core::array::from_fn(|lane| inputs[output_indices[lane]]);
        visit(&chunk, &output_indices, SIMD_LANES);
        i += SIMD_LANES;
    }

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

/// Group original input indices by challenge block count.
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

    /// Collect `(output_indices, active_lane_count)` for every visited chunk.
    fn visited(inputs: &[VerifyInput<'_>]) -> Vec<([usize; SIMD_LANES], usize)> {
        let mut order = Vec::new();
        let mut seen = Vec::new();
        for_each_simd_chunk(inputs, &mut order, |_, indices, active| {
            seen.push((*indices, active));
        });
        seen
    }

    #[test]
    fn every_input_is_visited_exactly_once_at_each_batch_size() {
        for count in 0..=(SIMD_LANES * 3 + 1) {
            let inputs = inputs(count, b"same");
            let mut covered = vec![0usize; count];
            for (indices, active) in visited(&inputs) {
                assert!(active <= SIMD_LANES);
                for &index in &indices[..active] {
                    covered[index] += 1;
                }
            }
            assert!(
                covered.iter().all(|&hits| hits == 1),
                "count {count} covered {covered:?}"
            );
        }
    }

    /// Padding lanes must stay addressable: a visitor that trusted the whole
    /// array would otherwise index past the caller's output slice.
    #[test]
    fn padding_lanes_hold_in_range_output_indices() {
        for count in 1..=(SIMD_LANES * 2 + 3) {
            for (indices, _) in visited(&inputs(count, b"uniform")) {
                assert!(
                    indices.iter().all(|&index| index < count),
                    "count {count} produced out-of-range indices {indices:?}"
                );
            }
        }
    }

    /// Mixed block counts take the bucketing path; uniform ones do not.
    #[test]
    fn bucketing_engages_only_for_mixed_block_counts() {
        let long = vec![0u8; 200];
        let uniform = inputs(SIMD_LANES * 2, b"short");
        assert!(!should_bucket_by_block_count(&uniform));

        let mut mixed = inputs(SIMD_LANES * 2, b"short");
        mixed[5].message = &long;
        assert!(should_bucket_by_block_count(&mixed));
        assert_ne!(
            challenge_block_count(long.len()),
            challenge_block_count(b"short".len())
        );

        // Too small to be worth reordering, even when the lengths differ.
        let mut small = inputs(SIMD_LANES, b"short");
        small[0].message = &long;
        assert!(!should_bucket_by_block_count(&small));
    }

    /// Bucketing sorts by block count, so the counts a batch visits never
    /// decrease; chunks are pure only where a bucket boundary happens to fall
    /// on a chunk boundary.
    #[test]
    fn bucketing_visits_block_counts_in_nondecreasing_order() {
        let long = vec![0u8; 200];
        let mut mixed = inputs(SIMD_LANES * 2, b"short");
        for index in [1, 4, 9, 14] {
            mixed[index].message = &long;
        }
        let visited_counts: Vec<usize> = visited(&mixed)
            .into_iter()
            .flat_map(|(indices, active)| {
                indices[..active]
                    .iter()
                    .map(|&i| challenge_block_count(mixed[i].message.len()))
                    .collect::<Vec<_>>()
            })
            .collect();
        assert!(
            visited_counts.windows(2).all(|pair| pair[0] <= pair[1]),
            "block counts are not sorted: {visited_counts:?}"
        );
    }

    /// A bucket split that lands on a chunk boundary yields pure chunks, which
    /// is the whole point: every lane then runs the same number of SHA-512
    /// compressions instead of masking the short lanes through the long tail.
    #[test]
    fn aligned_buckets_produce_single_block_count_chunks() {
        let long = vec![0u8; 200];
        let mut mixed = inputs(SIMD_LANES * 2, b"short");
        for index in 0..SIMD_LANES {
            mixed[index * 2].message = &long;
        }
        let chunks = visited(&mixed);
        assert_eq!(chunks.len(), 2);
        for (indices, active) in chunks {
            let counts: Vec<usize> = indices[..active]
                .iter()
                .map(|&i| challenge_block_count(mixed[i].message.len()))
                .collect();
            assert!(
                counts.windows(2).all(|pair| pair[0] == pair[1]),
                "chunk mixes block counts: {counts:?}"
            );
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
