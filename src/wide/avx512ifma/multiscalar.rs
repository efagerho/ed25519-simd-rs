use super::decode::{WideRPoint, decompress_deferred};
use super::field::WideFe;
use super::ladder_step::mul_s_base_minus_k_public;
use super::point::WidePoint;
use super::{LANES, mask_to_lanes};
use crate::batch::R_ENCODING_LEN;
use crate::edwards::{BasepointTableEntries, POINT_ENCODING_LEN, PointTable};
use crate::wide::PreparedChunk;

/// Chunks whose final inversion is shared. Each doubling halves the
/// inversion cost per chunk while adding three multiplies; past eight the
/// remaining inversion is small next to the buffering it would need.
pub(crate) const DALEK_BATCH: usize = 8;

/// An uncompressed Dalek verification result waiting to be compared with
/// the signature's encoded R point.
///
/// Eight candidates are normalized with one batch inversion before
/// their encodings are checked, instead of performing eight separate inversions.
pub(crate) struct DalekCandidate(pub(super) WidePoint);

/// ZIP-215 chunks whose `R` decompressions are interleaved pairwise, so
/// each inverse-square-root chain fills the other's IFMA latency gaps.
pub(crate) const ZIP215_BATCH: usize = 2;

/// A ZIP-215 ladder result waiting for its `R` point to be decompressed.
///
/// Two candidates queue two `R` decompressions whose exponentiation
/// chains are interleaved to hide dependent IFMA latency.
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
    fn score<const N: usize>(
        candidates: &[Zip215Candidate],
        bytes: &[[[u8; R_ENCODING_LEN]; LANES]],
    ) -> [([bool; LANES], [bool; LANES]); N] {
        let mut storage = core::mem::MaybeUninit::uninit();
        let bytes = bytes.try_into().expect("one R chunk per candidate");
        let (points, masks) = decompress_deferred::<N>(bytes, &mut storage);
        core::array::from_fn(|i| {
            (
                candidates[i]
                    .0
                    .subtract_affine_and_check_8_torsion(&points[i]),
                mask_to_lanes(masks[i]),
            )
        })
    }

    match candidates.len() {
        1 => {
            let [one] = score::<1>(candidates, r_bytes);
            [one, ([false; LANES], [false; LANES])]
        }
        2 => score::<2>(candidates, r_bytes),
        _ => unreachable!("the queue flushes at one or two chunks"),
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
    small_order: &mut [[bool; LANES]],
) {
    debug_assert_eq!(candidates.len(), encodings.len());
    debug_assert_eq!(candidates.len(), small_order.len());
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
        small_order[index] = candidates[index].0.is_small_order_lanes();
    }
    encodings[0] = candidates[0].0.compress_with_z_inverse(&accumulator);
    small_order[0] = candidates[0].0.is_small_order_lanes();
}

/// Identify small-order public keys from the already-built `[8]A` table entry.
pub(crate) fn public_key_small_order_lanes(
    public_key_tables: &[&PointTable; LANES],
) -> [bool; LANES] {
    let eight_a: [_; LANES] =
        core::array::from_fn(|lane| public_key_tables[lane].select_signed_cached_ref(8));
    let eight_a = WidePoint::from_cached_refs_without_t(&eight_a);
    let x_zero = eight_a.x.is_zero_lanes();
    let y_equals_z = eight_a.y.equals_lanes(&eight_a.z);
    core::array::from_fn(|lane| x_zero[lane] && y_equals_z[lane])
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
