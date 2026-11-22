use super::LANES;
use super::field::WideFe;

/// Eight extended Edwards points packed coordinate-wise for SIMD arithmetic.
///
/// One ladder round doubles eight accumulators and adds eight
/// table-selected multiples with the same sequence of vector instructions.
#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct WidePoint {
    pub(super) x: WideFe,
    pub(super) y: WideFe,
    pub(super) z: WideFe,
    pub(super) t: WideFe,
}

// The assembly ABI is four consecutive fields, each containing five vectors.
// Check both the nested layout and every coordinate offset at compile time.
const _: () = {
    use core::mem::{align_of, offset_of, size_of};
    assert!(size_of::<WideFe>() == 320);
    assert!(align_of::<WideFe>() == 64);
    assert!(offset_of!(WideFe, limbs) == 0);
    assert!(size_of::<WidePoint>() == 1280);
    assert!(align_of::<WidePoint>() == 64);
    assert!(offset_of!(WidePoint, x) == 0);
    assert!(offset_of!(WidePoint, y) == 320);
    assert!(offset_of!(WidePoint, z) == 640);
    assert!(offset_of!(WidePoint, t) == 960);
};

#[cfg(not(feature = "verify-asm-double4"))]
core::arch::global_asm!(include_str!("double4.S"), options(raw));

#[cfg(feature = "verify-asm-double4")]
core::arch::global_asm!(include_str!(concat!(env!("OUT_DIR"), "/double4-checked.S")));

#[cfg(not(feature = "verify-asm-cached-add"))]
core::arch::global_asm!(include_str!("add_cached.S"), options(raw));

#[cfg(feature = "verify-asm-cached-add")]
core::arch::global_asm!(include_str!(concat!(
    env!("OUT_DIR"),
    "/cached-add-checked.S"
)));

// These entries share private IFMA field kernels and the encoded-point layout.
core::arch::global_asm!(
    include_str!("torsion.S"),
    include_str!("pow22523.inc"),
    include_str!("point_encoding.inc"),
    include_str!("dalek_recompress.S"),
    include_str!("post_hash.inc"),
    include_str!("zip215.S"),
    include_str!("dalek.S"),
    include_str!("decompress_r.S"),
    options(raw)
);

impl WidePoint {
    /// Pack lane zero from eight duplicated points into independent lanes.
    pub(super) fn from_lane0_points(points: &[Self; LANES]) -> Self {
        let field = |pick: fn(&Self) -> WideFe| {
            WideFe::from_fields(&core::array::from_fn(|lane| pick(&points[lane]).lane0()))
        };
        Self {
            x: field(|point| point.x),
            y: field(|point| point.y),
            z: field(|point| point.z),
            t: field(|point| point.t),
        }
    }

    // Table-building points are strict, so small-bias `subtract` is valid.
    pub(super) fn add(&self, rhs: &Self) -> Self {
        self.add_impl::<false>(rhs)
    }
    pub(super) fn add_affine_rhs(&self, rhs: &Self) -> Self {
        debug_assert!(
            rhs.z.equals_lanes(&WideFe::one()).iter().all(|&eq| eq),
            "add_affine_rhs requires rhs.z == 1 in every lane"
        );
        self.add_impl::<true>(rhs)
    }
    // Always inline: `cold_add` shares this body, and letting that third
    // caller outline it puts a call in the hot table builder's `add`.
    #[inline(always)]
    fn add_impl<const AFFINE_RHS: bool>(&self, rhs: &Self) -> Self {
        let a = self.y.subtract(&self.x).multiply(&rhs.y.subtract(&rhs.x));
        let b = self.y.add_loose(&self.x).multiply(&rhs.y.add_loose(&rhs.x));
        let c = self.t.multiply(&rhs.t).multiply(&WideFe::two_d());
        let d = if AFFINE_RHS {
            self.z.double_loose()
        } else {
            self.z.multiply(&rhs.z).double_loose()
        };
        let e = b.subtract(&a);
        let f = d.subtract(&c);
        let g = d.add_loose(&c);
        let h = b.add_loose(&a);

        Self {
            x: e.multiply(&f),
            y: g.multiply(&h),
            t: e.multiply(&h),
            z: f.multiply(&g),
        }
    }

    /// Initialization-only copy of projective addition. Keeping its call
    /// sites separate preserves the hot table builder's inlining choices.
    #[inline(never)]
    pub(super) fn cold_add(&self, rhs: &Self) -> Self {
        self.add_impl::<false>(rhs)
    }
    pub(super) fn double(&self) -> Self {
        self.double_impl::<false>()
    }
    pub(super) fn double_from_affine(&self) -> Self {
        debug_assert!(
            self.z.equals_lanes(&WideFe::one()).iter().all(|&eq| eq),
            "double_from_affine requires z == 1 in every lane"
        );
        self.double_impl::<true>()
    }
    /// Initialization-only affine doubling, isolated so using SIMD during
    /// setup does not outline this operation in the verification hot path.
    #[inline(never)]
    pub(super) fn cold_double_from_affine(&self) -> Self {
        debug_assert!(
            self.z.equals_lanes(&WideFe::one()).iter().all(|&eq| eq),
            "cold_double_from_affine requires z == 1 in every lane"
        );
        self.double_impl::<true>()
    }
    #[inline(always)]
    fn double_impl<const AFFINE_Z: bool>(&self) -> Self {
        // Loose squares feed additive ops; use loose-input subtract/negate for
        // limb0 values up to ~2^60.
        let a = self.x.square_loose();
        let b = self.y.square_loose();
        let z2 = if AFFINE_Z {
            WideFe::one()
        } else {
            self.z.square_loose()
        };
        let e = self
            .x
            .add_loose(&self.y)
            .square_loose()
            .subtract_loose_sum(&a, &b);
        let g = b.subtract_loose(&a);
        // `f = b - a - 2*z^2`; the factor of two rides along in the subtract.
        let f = b.subtract_loose_sum_with_doubled_rhs(&a, &z2);
        let h = WideFe::negate_loose_sum(&a, &b);
        let t = e.multiply(&h);

        Self {
            x: e.multiply(&f),
            y: g.multiply(&h),
            t,
            z: f.multiply(&g),
        }
    }
}
