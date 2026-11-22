use super::LANES;
#[cfg(not(all(feature = "asm", target_os = "linux", target_pointer_width = "64")))]
use super::decode::WideRPoint;
#[cfg(not(all(feature = "asm", target_os = "linux", target_pointer_width = "64")))]
use super::ladder_step::mul_s_base_minus_k_public;
use super::point::WidePoint;
use crate::batch::R_ENCODING_LEN;
#[cfg(not(all(feature = "asm", target_os = "linux", target_pointer_width = "64")))]
use crate::edwards::{BasepointTableEntries, PointTable};
#[cfg(not(all(feature = "asm", target_os = "linux", target_pointer_width = "64")))]
use crate::wide::PreparedChunk;

/// Chunks whose final inversion is shared. Each doubling halves the
/// inversion cost per chunk while adding three multiplies; past eight the
/// remaining inversion is small next to the buffering it would need.
pub(crate) const DALEK_BATCH: usize = 8;

/// An uncompressed Dalek verification result waiting to be compared with
/// the signature's encoded R point.
///
/// Up to eight queued chunks share the inversion used to recover affine X.
#[repr(transparent)]
pub(crate) struct DalekCandidate(pub(super) WidePoint);

impl core::fmt::Debug for DalekCandidate {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("DalekCandidate")
            .finish_non_exhaustive()
    }
}

#[inline(never)]
#[cfg(not(all(feature = "asm", target_os = "linux", target_pointer_width = "64")))]
pub(crate) fn prepare_dalek_candidate(
    prepared: &PreparedChunk<'_>,
    base_table: &BasepointTableEntries,
) -> DalekCandidate {
    DalekCandidate(mul_s_base_minus_k_public::<false>(base_table, prepared))
}

/// Bit j of byte i is set when candidate (i,j) has the supplied encoding
/// and passes the Dalek small-order check. Unused bytes are zero.
pub(crate) fn check_dalek_candidates(
    candidates: &[DalekCandidate],
    r_bytes: &[[[u8; R_ENCODING_LEN]; LANES]],
) -> [u8; DALEK_BATCH] {
    assert_eq!(candidates.len(), r_bytes.len());
    assert!(candidates.len() <= DALEK_BATCH);

    #[cfg(all(feature = "asm", target_os = "linux", target_pointer_width = "64"))]
    {
        const _: () = assert!(DALEK_BATCH == 8 && R_ENCODING_LEN == 32);
        unsafe extern "C" {
            fn ed25519_simd_dalek_recompress(points: *const u8, r: *const u8, n: usize) -> u64;
        }
        // SAFETY: DalekCandidate is transparent over the aligned WidePoint ABI.
        // Both arrays cover n read-only chunks. The ladder bounds XYZ limbs to
        // 52 bits and only produces projective points with nonzero Z.
        unsafe {
            ed25519_simd_dalek_recompress(
                candidates.as_ptr().cast(),
                r_bytes.as_ptr().cast(),
                candidates.len(),
            )
            .to_le_bytes()
        }
    }

    #[cfg(not(all(feature = "asm", target_os = "linux", target_pointer_width = "64")))]
    check_dalek_candidates_rust(candidates, r_bytes)
}

#[cfg(not(all(feature = "asm", target_os = "linux", target_pointer_width = "64")))]
fn check_dalek_candidates_rust(
    candidates: &[DalekCandidate],
    r_bytes: &[[[u8; R_ENCODING_LEN]; LANES]],
) -> [u8; DALEK_BATCH] {
    use super::field::WideFe;

    let mut masks = [0; DALEK_BATCH];
    let Some(first) = candidates.first() else {
        return masks;
    };
    let mut product = first.0.z;
    let mut prefix = [WideFe::one(); DALEK_BATCH];
    prefix[0] = product;
    for (index, candidate) in candidates.iter().enumerate().skip(1) {
        product = product.multiply(&candidate.0.z);
        prefix[index] = product;
    }

    let mut accumulator = product.invert();
    for i in (0..candidates.len()).rev() {
        let inverse = if i == 0 {
            accumulator
        } else {
            let inverse = prefix[i - 1].multiply(&accumulator);
            accumulator = accumulator.multiply(&candidates[i].0.z);
            inverse
        };
        let encoding = candidates[i].0.compress_with_z_inverse(&inverse);
        let small_order = candidates[i].0.is_small_order_lanes();
        for lane in 0..LANES {
            let matches = encoding[lane] == r_bytes[i][lane] && !small_order[lane];
            masks[i] |= u8::from(matches) << lane;
        }
    }
    masks
}

/// Identify small-order public keys from the already-built `[8]A` table entry.
#[cfg(not(all(feature = "asm", target_os = "linux", target_pointer_width = "64")))]
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
#[cfg(not(all(feature = "asm", target_os = "linux", target_pointer_width = "64")))]
pub(crate) fn verify_prepared_dalek_decompressed_r(
    prepared: &PreparedChunk<'_>,
    r: &WideRPoint,
    base_table: &BasepointTableEntries,
) -> [bool; LANES] {
    let combined = mul_s_base_minus_k_public::<false>(base_table, prepared);
    combined.equals_affine_lanes(&r.point)
}
