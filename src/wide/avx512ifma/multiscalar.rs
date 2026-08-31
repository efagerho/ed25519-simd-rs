use super::decode::{WideRPoint, decompress_finish, decompress_r_points, decompress_setup};
use super::field::WideFe;
use super::point::WidePoint;
use super::{LANES, mask_to_lanes};
use crate::batch::R_ENCODING_LEN;
use crate::edwards::{
    BasepointTableEntries, POINT_ENCODING_LEN, PointTable, select_signed_affine_cached_ref,
};
use crate::scalar::Radix16;
use crate::wide::PreparedChunk;

/// Chunks whose final inversion is shared. Each doubling halves the
/// inversion cost per chunk while adding three multiplies; past eight the
/// remaining inversion is small next to the buffering it would need.
pub(crate) const DALEK_BATCH: usize = 8;

/// An uncompressed Dalek verification result waiting to be compared with
/// the signature's encoded R point.
pub(crate) struct DalekCandidate(pub(super) WidePoint);

/// ZIP-215 chunks whose `R` decompressions are interleaved pairwise, so
/// each inverse-square-root chain fills the other's IFMA latency gaps.
pub(crate) const ZIP215_BATCH: usize = 2;

/// A ZIP-215 ladder result waiting for its `R` point to be decompressed.
pub(crate) struct Zip215Candidate(pub(super) WidePoint);

// A queued candidate is an opaque curve point; name it and stop.
macro_rules! opaque_debug {
    ($($type:ident),+) => {$(
        impl core::fmt::Debug for $type {
            fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                formatter.debug_struct(stringify!($type)).finish_non_exhaustive()
            }
        }
    )+};
}
opaque_debug!(Zip215Candidate, DalekCandidate);
// ZIP-215 cofactored verification: [8](sB - kA - R) == identity.
#[inline(never)]
pub(crate) fn verify_prepared_zip215(
    prepared: &PreparedChunk<'_>,
    r: &WideRPoint,
    base_table: &BasepointTableEntries,
) -> [bool; LANES] {
    let combined = mul_s_base_minus_k_public::<true>(base_table, prepared);
    combined.subtract_affine_and_check_8_torsion(&r.point)
}

#[inline(never)]
pub(crate) fn prepare_zip215_candidate(
    prepared: &PreparedChunk<'_>,
    base_table: &BasepointTableEntries,
) -> Zip215Candidate {
    Zip215Candidate(mul_s_base_minus_k_public::<true>(base_table, prepared))
}

/// Score up to [`ZIP215_BATCH`] queued chunks, decompressing a pair of `R`
/// chunks through interleaved inverse-square-root chains. Returns
/// per-chunk `(equation_holds, r_valid)` lane flags.
pub(crate) fn check_zip215_candidates(
    candidates: &[Zip215Candidate],
    r_bytes: &[[[u8; R_ENCODING_LEN]; LANES]],
) -> [([bool; LANES], [bool; LANES]); ZIP215_BATCH] {
    debug_assert_eq!(candidates.len(), r_bytes.len());
    let empty = ([false; LANES], [false; LANES]);
    match candidates {
        [single] => {
            let (r, r_mask) = decompress_r_points(&r_bytes[0]);
            let holds = single.0.subtract_affine_and_check_8_torsion(&r.point);
            [(holds, mask_to_lanes(r_mask)), empty]
        }
        [first, second] => {
            let setup_a = decompress_setup(&r_bytes[0]);
            let setup_b = decompress_setup(&r_bytes[1]);
            let (pow_a, pow_b) = WideFe::pow_p_minus_5_over_8_x2(&setup_a.uv, &setup_b.uv);
            let (r_a, mask_a, _) = decompress_finish::<true, false>(setup_a, pow_a);
            let (r_b, mask_b, _) = decompress_finish::<true, false>(setup_b, pow_b);
            [
                (
                    first.0.subtract_affine_and_check_8_torsion(&r_a),
                    mask_to_lanes(mask_a),
                ),
                (
                    second.0.subtract_affine_and_check_8_torsion(&r_b),
                    mask_to_lanes(mask_b),
                ),
            ]
        }
        _ => unreachable!("the queue flushes at ZIP215_BATCH chunks"),
    }
}

#[inline(never)]
pub(crate) fn prepare_dalek_candidate(
    prepared: &PreparedChunk<'_>,
    base_table: &BasepointTableEntries,
) -> DalekCandidate {
    DalekCandidate(mul_s_base_minus_k_public::<false>(base_table, prepared))
}

/// Compress up to [`DALEK_BATCH`] chunks sharing a single field inversion.
///
/// Montgomery's trick: invert the running product of every `Z`, then walk
/// back down recovering each reciprocal with one multiply. That trades
/// `n - 1` inversions for `3(n - 1)` multiplies, and an inversion costs
/// roughly 265 field operations against a multiply's one.
pub(crate) fn compress_dalek_candidates(
    candidates: &[DalekCandidate],
    encodings: &mut [[[u8; POINT_ENCODING_LEN]; LANES]],
) {
    debug_assert_eq!(candidates.len(), encodings.len());
    debug_assert!(candidates.len() <= DALEK_BATCH);
    if candidates.is_empty() {
        return;
    }

    let mut product = candidates[0].0.z;
    let mut prefix = [WideFe::one(); DALEK_BATCH];
    prefix[0] = product;
    for (index, candidate) in candidates.iter().enumerate().skip(1) {
        product = product.multiply(&candidate.0.z);
        prefix[index] = product;
    }

    // Walking back down lets each reciprocal be consumed as it is formed,
    // so no array of inverses is ever materialized.
    let mut accumulator = product.invert();
    for index in (1..candidates.len()).rev() {
        let z = &candidates[index].0.z;
        let inverse = prefix[index - 1].multiply(&accumulator);
        accumulator = accumulator.multiply(z);
        encodings[index] = candidates[index].0.compress_with_z_inverse(&inverse);
    }
    encodings[0] = candidates[0].0.compress_with_z_inverse(&accumulator);
}

#[inline(never)]
pub(crate) fn verify_prepared_dalek_decompressed_r(
    prepared: &PreparedChunk<'_>,
    r: &WideRPoint,
    base_table: &BasepointTableEntries,
) -> [bool; LANES] {
    let combined = mul_s_base_minus_k_public::<false>(base_table, prepared);
    combined.equals_affine_lanes(&r.point)
}

// Only ZIP-215's final torsion subtraction needs T.
pub(super) fn mul_s_base_minus_k_public<const NEED_T: bool>(
    base_table: &BasepointTableEntries,
    prepared: &PreparedChunk<'_>,
) -> WidePoint {
    let public_key_tables = &prepared.public_key_tables;
    let s_digits = prepared.s_digits;
    let k_digits = prepared.k_digits;

    // Recover a projective point from the cached top digit; the next
    // doubling does not need `T`.
    let selected: [_; LANES] = core::array::from_fn(|lane| {
        public_key_tables[lane].select_signed_cached_ref(-k_digits[lane][63])
    });
    let mut acc = WidePoint::from_cached_refs_without_t(&selected);

    // Continue at digit 62; reduced scalars have no digit above 63.
    acc.double_four_times_assign();
    add_base_pair_digit(&mut acc, base_table, s_digits, 31);
    subtract_public_key_digit_before_double(&mut acc, public_key_tables, k_digits, 62);

    // These public-key additions feed doublings, which do not use `T`.
    for pair in (1..31).rev() {
        acc.double_four_times_assign();
        subtract_public_key_digit_before_double(
            &mut acc,
            public_key_tables,
            k_digits,
            pair * 2 + 1,
        );

        acc.double_four_times_assign();
        add_base_pair_digit(&mut acc, base_table, s_digits, pair);
        subtract_public_key_digit_before_double(&mut acc, public_key_tables, k_digits, pair * 2);
    }

    acc.double_four_times_assign();
    subtract_public_key_digit_before_double(&mut acc, public_key_tables, k_digits, 1);
    acc.double_four_times_assign();
    add_base_pair_digit(&mut acc, base_table, s_digits, 0);
    if NEED_T {
        subtract_public_key_digit(&mut acc, public_key_tables, k_digits, 0);
    } else {
        subtract_public_key_digit_before_double(&mut acc, public_key_tables, k_digits, 0);
    }
    acc
}

#[inline]
fn add_base_pair_digit(
    acc: &mut WidePoint,
    base_table: &BasepointTableEntries,
    s_digits: &[Radix16; LANES],
    pair: usize,
) {
    let selected: [_; LANES] = core::array::from_fn(|lane| {
        select_signed_affine_cached_ref(base_table, base_pair_digit(&s_digits[lane], pair))
    });
    acc.add_affine_cached_refs_assign(&selected);
}

#[inline]
fn subtract_public_key_digit(
    acc: &mut WidePoint,
    public_key_tables: &[&PointTable; LANES],
    k_digits: &[Radix16; LANES],
    index: usize,
) {
    let selected: [_; LANES] = core::array::from_fn(|lane| {
        public_key_tables[lane].select_signed_cached_ref(-k_digits[lane][index])
    });
    acc.add_cached_refs_assign(&selected, true);
}

#[inline]
fn subtract_public_key_digit_before_double(
    acc: &mut WidePoint,
    public_key_tables: &[&PointTable; LANES],
    k_digits: &[Radix16; LANES],
    index: usize,
) {
    let selected: [_; LANES] = core::array::from_fn(|lane| {
        public_key_tables[lane].select_signed_cached_ref(-k_digits[lane][index])
    });
    acc.add_cached_refs_assign(&selected, false);
}

// Fold a radix-16 digit pair into a bounded radix-256 base-table digit.
#[inline(always)]
fn base_pair_digit(digits: &Radix16, pair: usize) -> i16 {
    digits[pair * 2] as i16 + ((digits[pair * 2 + 1] as i16) << 4)
}
