use super::field::WideFe;
use super::point::WidePoint;
use super::tables::{build_lane0_table_from_point, build_tables_from_point};
use super::{LANES, mask_to_lanes};
use crate::batch::R_ENCODING_LEN;
use crate::edwards::{POINT_ENCODING_LEN, PointTable};
use crate::field::Fe51;
use crate::input::PUBLIC_KEY_LEN;

/// Eight decompressed signature `R` points plus optional Dalek validity state.
///
/// One bit of `x_zero_mask` rejects a lane whose encoding requests
/// negative zero while the packed point continues through the SIMD ladder.
pub(crate) struct WideRPoint {
    pub(super) point: WidePoint,
    x_zero_mask: Option<u8>,
}
impl WideRPoint {
    /// Dalek-invalid negative-zero lanes.
    pub(crate) fn x_zero_lanes(&self) -> [bool; LANES] {
        let mask = self
            .x_zero_mask
            .expect("x-zero lanes were not tracked for this decode");
        mask_to_lanes(mask)
    }

    /// Lanes whose decoded points have order dividing the cofactor.
    pub(crate) fn small_order_lanes(&self) -> [bool; LANES] {
        self.point.is_small_order_lanes()
    }
}

/// Decompress one SIMD chunk of `R` points and return a per-lane validity mask.
pub(crate) fn decompress_r_points(r_bytes: &[[u8; R_ENCODING_LEN]; LANES]) -> (WideRPoint, u8) {
    let (point, mask) = decompress_points_wide(r_bytes);
    (
        WideRPoint {
            point,
            x_zero_mask: None,
        },
        mask,
    )
}

/// Decode keys and `R` together, interleaving their inverse-square-root chains.
#[inline(never)]
pub(crate) fn decode_keys_and_decompress_r<const DALEK: bool>(
    keys: &[[u8; PUBLIC_KEY_LEN]; LANES],
    r_bytes: &[[u8; R_ENCODING_LEN]; LANES],
    key_tables: &mut [Option<PointTable>; LANES],
) -> (u8, WideRPoint, u8) {
    let ((kp, kmask), (rp, rmask, x_zero_mask)) =
        decompress_two_point_chunks_wide::<DALEK>(keys, r_bytes);
    build_tables_from_point(kp, key_tables);
    (
        kmask,
        WideRPoint {
            point: rp,
            x_zero_mask,
        },
        rmask,
    )
}

/// Decode one public key and build its cached table with the SIMD field
/// implementation. All lanes contain the same public input; only lane zero
/// is materialized into the returned table.
pub(crate) fn decode_public_key_table(encoded: &[u8; PUBLIC_KEY_LEN]) -> Option<PointTable> {
    let (point, mask) = cold_decompress_points_wide(&[*encoded; LANES]);
    if mask & 1 == 0 {
        return None;
    }
    Some(build_lane0_table_from_point(point))
}
/// Decompression state before the inverse-square-root exponentiation.
///
/// Retaining two setups lets their exponentiation chains alternate
/// IFMA operations so one chain fills the other's multiplication latency.
pub(super) struct DecompressSetup {
    u: WideFe,
    v: WideFe,
    pub(super) uv: WideFe, // raised to (p-5)/8
    y: WideFe,
    x_sign_mask: u8,
}

pub(super) fn decompress_setup(bytes: &[[u8; POINT_ENCODING_LEN]; LANES]) -> DecompressSetup {
    let mut y_fields = core::array::from_fn(|_| Fe51::zero());
    let mut x_sign_mask = 0u8;

    for (lane, byte_arr) in bytes.iter().enumerate() {
        x_sign_mask |= (byte_arr[31] >> 7) << lane;
        let mut y_bytes = *byte_arr;
        y_bytes[31] &= 0x7f;
        // ZIP-215/Dalek decoding treats y modulo p.
        y_fields[lane] = Fe51::from_bytes_unchecked(&y_bytes);
    }

    let y = WideFe::from_fields(&y_fields);
    let yy = y.square();
    let u = yy.subtract(&WideFe::one());
    let v = WideFe::one().add(&WideFe::d().multiply(&yy));
    let uv = u.multiply(&v);
    DecompressSetup {
        u,
        v,
        uv,
        y,
        x_sign_mask,
    }
}

pub(super) fn decompress_finish<const COMPUTE_T: bool, const TRACK_X_ZERO: bool>(
    s: DecompressSetup,
    pow: WideFe,
) -> (WidePoint, u8, Option<u8>) {
    let mut x = s.u.multiply(&pow);

    let vx2 = s.v.multiply(&x.square());
    let primary_root_mask = vx2.equals_mask(&s.u);

    let x_alt = x.multiply(&WideFe::sqrt_m1());
    // The alternate root is valid iff the existing `vx2` equals `-u`.
    let alternate_root_mask = vx2.add_loose(&s.u).is_zero_mask();

    let use_alternate_root_mask = !primary_root_mask & alternate_root_mask;
    let valid_mask = primary_root_mask | alternate_root_mask;

    x = x.blend(use_alternate_root_mask, &x_alt);

    // Points outside `valid_mask` are garbage.
    let (x_odd_mask, x_zero_mask) = if TRACK_X_ZERO {
        let (odd, zero) = x.odd_and_zero_masks();
        (odd, Some(zero))
    } else {
        (x.is_odd_mask(), None)
    };
    let x_neg = x.negate();
    let negate_mask = x_odd_mask ^ s.x_sign_mask;
    x = x.blend(negate_mask, &x_neg);

    let t = if COMPUTE_T {
        x.multiply(&s.y)
    } else {
        WideFe::zero()
    };
    (
        WidePoint {
            x,
            y: s.y,
            z: WideFe::one(),
            t,
        },
        valid_mask,
        x_zero_mask,
    )
}

/// Decompress one SIMD chunk of compressed Edwards points with per-lane validity.
pub(super) fn decompress_points_wide(bytes: &[[u8; POINT_ENCODING_LEN]; LANES]) -> (WidePoint, u8) {
    let s = decompress_setup(bytes);
    let pow = s.uv.pow_p_minus_5_over_8();
    let (point, mask, _) = decompress_finish::<true, false>(s, pow);
    (point, mask)
}

/// Initialization-only decompression, kept distinct so setup work cannot
/// change inlining in verification's single-chunk decompression path.
#[inline(never)]
pub(super) fn cold_decompress_points_wide(
    bytes: &[[u8; POINT_ENCODING_LEN]; LANES],
) -> (WidePoint, u8) {
    let s = decompress_setup(bytes);
    let pow = s.uv.cold_pow_p_minus_5_over_8();
    let (point, mask, _) = decompress_finish::<true, false>(s, pow);
    (point, mask)
}

/// Decompress two independent SIMD chunks, interleaving the two
/// inverse-square-root chains so each fills the other's IFMA latency gaps.
pub(super) fn decompress_two_point_chunks_wide<const MINIMIZE_B_FOR_DALEK: bool>(
    a_bytes: &[[u8; POINT_ENCODING_LEN]; LANES],
    b_bytes: &[[u8; POINT_ENCODING_LEN]; LANES],
) -> ((WidePoint, u8), (WidePoint, u8, Option<u8>)) {
    let sa = decompress_setup(a_bytes);
    let sb = decompress_setup(b_bytes);
    let (pa, pb) = WideFe::pow_p_minus_5_over_8_x2(&sa.uv, &sb.uv);
    let (a, a_mask, _) = decompress_finish::<true, false>(sa, pa);
    let b = if MINIMIZE_B_FOR_DALEK {
        decompress_finish::<false, true>(sb, pb)
    } else {
        decompress_finish::<true, false>(sb, pb)
    };
    ((a, a_mask), b)
}
