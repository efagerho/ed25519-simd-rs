use super::LANES;
use super::field::WideFe;
use crate::edwards::{AffineCachedPoint, CachedPoint, POINT_ENCODING_LEN};
use crate::field::Fe51;

/// Eight extended Edwards points packed coordinate-wise for SIMD arithmetic.
///
/// One ladder round doubles eight accumulators and adds eight
/// table-selected multiples with the same sequence of vector instructions.
#[derive(Clone, Copy)]
pub(super) struct WidePoint {
    pub(super) x: WideFe,
    pub(super) y: WideFe,
    pub(super) z: WideFe,
    pub(super) t: WideFe,
}

/// Per-lane cached points selected from either projective or affine tables.
///
/// The affine variant omits cached `2Z`; mixed addition substitutes
/// a vector doubling while using the same coordinate-transposition path.
#[derive(Clone, Copy)]
enum SelectedCachedRefs<'a> {
    Projective(&'a [&'a CachedPoint; LANES]),
    Affine(&'a [&'a AffineCachedPoint; LANES]),
}

impl SelectedCachedRefs<'_> {
    /// Transpose one cached coordinate. The pickers differ because an affine
    /// point omits `2*Z`, shifting `t2d` down a slot.
    #[inline(always)]
    fn transpose(
        self,
        projective: impl Fn(&CachedPoint) -> &Fe51,
        affine: impl Fn(&AffineCachedPoint) -> &Fe51,
    ) -> WideFe {
        match self {
            Self::Projective(points) => {
                WideFe::from_field_refs(&core::array::from_fn(|lane| projective(points[lane])))
            }
            Self::Affine(points) => {
                WideFe::from_field_refs(&core::array::from_fn(|lane| affine(points[lane])))
            }
        }
    }

    #[inline(always)]
    fn y_plus_x(self) -> WideFe {
        self.transpose(|p| p.coords().0, |p| p.coords().0)
    }

    #[inline(always)]
    fn y_minus_x(self) -> WideFe {
        self.transpose(|p| p.coords().1, |p| p.coords().1)
    }

    #[inline(always)]
    fn t2d(self) -> WideFe {
        self.transpose(|p| p.coords().3, |p| p.coords().2)
    }

    /// The cached `2*Z`, or `None` for an affine point whose `Z` is one.
    #[inline(always)]
    fn projective_z2(self) -> Option<WideFe> {
        match self {
            Self::Projective(points) => {
                Some(WideFe::from_field_refs(&core::array::from_fn(|lane| {
                    points[lane].coords().2
                })))
            }
            Self::Affine(_) => None,
        }
    }
}
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

    /// Recover `(X:Y:Z)` without `T`; callers must double before an
    /// extended-coordinate operation.
    #[inline(never)]
    pub(super) fn from_cached_refs_without_t(points: &[&CachedPoint; LANES]) -> Self {
        let field = |pick: fn(&CachedPoint) -> &Fe51| {
            WideFe::from_field_refs(&core::array::from_fn(|lane| pick(points[lane])))
        };
        let y_plus_x = field(|p| p.coords().0);
        let y_minus_x = field(|p| p.coords().1);

        Self {
            x: y_plus_x.subtract(&y_minus_x),
            y: y_plus_x.add_loose(&y_minus_x),
            z: field(|p| p.coords().2),
            t: WideFe::zero(),
        }
    }
    #[cfg(test)]
    pub(super) fn compress(&self) -> [[u8; POINT_ENCODING_LEN]; LANES] {
        let zinv = self.z.invert();
        self.compress_with_z_inverse(&zinv)
    }
    pub(super) fn compress_with_z_inverse(
        &self,
        zinv: &WideFe,
    ) -> [[u8; POINT_ENCODING_LEN]; LANES] {
        let x = self.x.multiply(zinv);
        let y = self.y.multiply(zinv);
        let x_odd_mask = x.is_odd_mask();
        let mut bytes = y.to_bytes_lanes();
        for (lane, encoding) in bytes.iter_mut().enumerate() {
            encoding[31] |= ((x_odd_mask >> lane) & 1) << 7;
        }
        bytes
    }
    /// Compare with a freshly decompressed point whose `z` is one.
    pub(super) fn equals_affine_lanes(&self, affine: &Self) -> [bool; LANES] {
        debug_assert!(
            affine.z.equals_lanes(&WideFe::one()).iter().all(|&eq| eq),
            "equals_affine_lanes requires z == 1 in every lane"
        );
        let x = affine.x.multiply(&self.z);
        let y = affine.y.multiply(&self.z);
        let x_equal = self.x.equals_lanes(&x);
        let y_equal = self.y.equals_lanes(&y);
        core::array::from_fn(|lane| x_equal[lane] && y_equal[lane])
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
    pub(super) fn add_impl<const AFFINE_RHS: bool>(&self, rhs: &Self) -> Self {
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
    /// Add the per-lane cached points selected for one digit.
    ///
    /// Transpose each cached field just before use; gathering all four needs
    /// 20 live ZMM registers and spills.
    #[inline(always)]
    pub(super) fn add_cached_refs_assign(
        &mut self,
        points: &[&CachedPoint; LANES],
        compute_t: bool,
    ) {
        self.add_selected_cached_refs_assign(SelectedCachedRefs::Projective(points), compute_t);
    }
    /// Mixed addition with an affine cached point. The cached point has
    /// `Z = 1`, so `2*Z1*Z2` is just a doubling of the accumulator's `Z`.
    #[inline(always)]
    pub(super) fn add_affine_cached_refs_assign(&mut self, points: &[&AffineCachedPoint; LANES]) {
        self.add_selected_cached_refs_assign(SelectedCachedRefs::Affine(points), true);
    }
    #[inline(never)]
    fn add_selected_cached_refs_assign(&mut self, points: SelectedCachedRefs<'_>, compute_t: bool) {
        // Loose products feed additive ops; use loose-input subtracts for limb0
        // values up to ~2^60.
        let a = self.y.subtract(&self.x).multiply_loose(&points.y_minus_x());
        let b = self.y.add_loose(&self.x).multiply_loose(&points.y_plus_x());
        let e = b.subtract_loose(&a);
        let h = b.add_loose(&a);
        let c = self.t.multiply_loose(&points.t2d());
        let d = match points.projective_z2() {
            Some(z2) => self.z.multiply_loose(&z2),
            None => self.z.double_loose(),
        };
        let f = d.subtract_loose(&c);
        let g = d.add_loose(&c);

        self.x = e.multiply(&f);
        self.t = if compute_t {
            e.multiply(&h)
        } else {
            WideFe::zero()
        };
        self.z = f.multiply(&g);
        self.y = g.multiply(&h);
    }
    #[cfg(test)]
    pub(super) fn subtract(&self, rhs: &Self) -> Self {
        self.add(&rhs.negate())
    }
    /// Return whether `self - rhs` is killed by the Ed25519 cofactor.
    ///
    /// For `Q = self - rhs`, test `x(2Q)*y(2Q) == 0` via its numerator
    /// `E*H`, avoiding materialization of `Q` or `2Q`. Requires `rhs.z == 1`.
    pub(super) fn subtract_affine_and_check_8_torsion(&self, rhs: &Self) -> [bool; LANES] {
        debug_assert!(
            rhs.z.equals_lanes(&WideFe::one()).iter().all(|&eq| eq),
            "ZIP-215 R subtraction requires affine rhs"
        );

        // Strongly-unified mixed subtraction.  Only X and Y are needed.
        let a = self.y.subtract(&self.x).multiply(&rhs.y.add_loose(&rhs.x));
        let b = self.y.add_loose(&self.x).multiply(&rhs.y.subtract(&rhs.x));
        let c = self.t.multiply(&rhs.t).multiply(&WideFe::two_d());
        let d = self.z.double_loose();
        let e = b.subtract(&a);
        let f = d.add_loose(&c);
        let g = d.subtract(&c);
        let h = b.add_loose(&a);
        let x = e.multiply(&f);
        let y = g.multiply(&h);

        // T(2Q) = E*H, where E = 2XY and H = -(X^2+Y^2).
        let xx = x.square_loose();
        let yy = y.square_loose();
        let double_e = x.add_loose(&y).square_loose().subtract_loose_sum(&xx, &yy);
        let double_h = WideFe::negate_loose_sum(&xx, &yy);
        double_e.multiply(&double_h).is_zero_lanes()
    }
    #[cfg(test)]
    pub(super) fn negate(&self) -> Self {
        Self {
            x: self.x.negate(),
            y: self.y,
            z: self.z,
            t: self.t.negate(),
        }
    }
    pub(super) fn double(&self) -> Self {
        self.double_impl::<true, false>()
    }
    pub(super) fn double_from_affine(&self) -> Self {
        debug_assert!(
            self.z.equals_lanes(&WideFe::one()).iter().all(|&eq| eq),
            "double_from_affine requires z == 1 in every lane"
        );
        self.double_impl::<true, true>()
    }
    /// Initialization-only affine doubling, isolated so using SIMD during
    /// setup does not outline this operation in the verification hot path.
    #[inline(never)]
    pub(super) fn cold_double_from_affine(&self) -> Self {
        debug_assert!(
            self.z.equals_lanes(&WideFe::one()).iter().all(|&eq| eq),
            "cold_double_from_affine requires z == 1 in every lane"
        );
        self.double_impl::<true, true>()
    }
    pub(super) fn double_without_t(&self) -> Self {
        self.double_impl::<false, false>()
    }

    /// In place so `acc = acc.double_four_times()`'s 1280-byte return
    /// copy never happens; the last double writes straight into `self`.
    #[inline(never)]
    pub(super) fn double_four_times_assign(&mut self) {
        let tripled = self
            .double_without_t()
            .double_without_t()
            .double_without_t();
        tripled.double_into(self);
    }
    /// Inlined body stores its result directly through `out`, which a
    /// returned `Self` assigned across a call boundary does not.
    #[inline(always)]
    pub(super) fn double_into(&self, out: &mut Self) {
        *out = self.double_impl::<true, false>();
    }
    // Always inline: callers embed it exactly once each, and the inlined
    // body lets an `_into` destination receive direct stores.
    #[inline(always)]
    pub(super) fn double_impl<const COMPUTE_T: bool, const AFFINE_Z: bool>(&self) -> Self {
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
        let t = if COMPUTE_T {
            e.multiply(&h)
        } else {
            WideFe::zero()
        };

        Self {
            x: e.multiply(&f),
            y: g.multiply(&h),
            t,
            z: f.multiply(&g),
        }
    }
}
