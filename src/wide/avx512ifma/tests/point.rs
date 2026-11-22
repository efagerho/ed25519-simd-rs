//! Rust-side adapters for exercising private point kernels and inspecting their output.
#[cfg(debug_assertions)]
use super::super::field::limbs_are_ifma_operands;
use super::*;
use crate::field::Fe51;

unsafe extern "C" {
    /// SysV: RDI points to one exclusive, initialized `WidePoint`.
    ///
    /// For X, Y and Z, each lane must have limb 0 < 2^60,
    /// limb 1 + (limb 0 >> 51) < 2^52, and limbs 2..4 < 2^52.
    /// Incoming T is ignored, including its limb bounds. Writes all four
    /// coordinates; output limbs 0, 2..4 are < 2^51 and limb 1 < 2^52.
    /// See double4.S for the arithmetic, scratch and register contract.
    // Use a byte pointer because Rust's SIMD vector types are not C types.
    fn ed25519_simd_double4_ifma(point: *mut u8);

    /// In-place addition with staged (Y-X), (Y+X), 2dT, and optional 2Z.
    /// `affine` and `compute_t` are 0 or 1. Every input limb is < 2^52.
    /// Buffers are disjoint and 64-byte aligned. See add_cached.S for the
    /// complete ABI and arithmetic contract, proved in verification/crate/cached_add.
    fn ed25519_simd_add_cached_ifma(point: *mut u8, cached: *const u8, compute_t: u64, affine: u64);

    fn ed25519_simd_check_8_torsion_ifma(point: *const u8, affine: *const u8) -> u8;
    fn ed25519_simd_small_order_ifma(point: *const u8) -> u8;
}

impl WidePoint {
    pub(super) fn add_cached_refs_assign(
        &mut self,
        points: &[&CachedPoint; LANES],
        compute_t: bool,
    ) {
        let field = |pick: fn(&CachedPoint) -> &Fe51| {
            WideFe::from_field_refs(&core::array::from_fn(|j| pick(points[j])))
        };
        let fields = [
            field(|p| p.coords().1),
            field(|p| p.coords().0),
            field(|p| p.coords().3),
            field(|p| p.coords().2),
        ];
        self.add_staged_cached_assign(&fields, compute_t);
    }

    pub(super) fn add_affine_cached_refs_assign(&mut self, points: &[&AffineCachedPoint; LANES]) {
        let field = |pick: fn(&AffineCachedPoint) -> &Fe51| {
            WideFe::from_field_refs(&core::array::from_fn(|j| pick(points[j])))
        };
        let fields = [
            field(|p| p.coords().1),
            field(|p| p.coords().0),
            field(|p| p.coords().2),
        ];
        self.add_staged_cached_assign(&fields, true);
    }

    #[inline(always)]
    fn add_staged_cached_assign<const N: usize>(&mut self, fields: &[WideFe; N], compute_t: bool) {
        const {
            assert!(N == 3 || N == 4);
        }
        #[cfg(debug_assertions)]
        for field in [&self.x, &self.y, &self.z, &self.t]
            .into_iter()
            .chain(fields)
        {
            debug_assert!(limbs_are_ifma_operands(&field.limbs));
        }
        // SAFETY: the array length determines the affine flag and the exact
        // readable extent. Its aligned fields are disjoint from the exclusive
        // point borrow. Both producers supply 52-bit limbs.
        unsafe {
            ed25519_simd_add_cached_ifma(
                core::ptr::from_mut(self).cast(),
                fields.as_ptr().cast(),
                u64::from(compute_t),
                u64::from(N == 3),
            );
        }
    }

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

        #[cfg(debug_assertions)]
        for field in [&self.x, &self.y, &self.z, &self.t, &rhs.x, &rhs.y, &rhs.t] {
            debug_assert!(limbs_are_ifma_operands(&field.limbs));
        }
        // SAFETY: Both borrows are readable WidePoints with the statically checked layout.
        // The ladder and decompressor produce 52-bit limbs in the fields read.
        let mask = unsafe {
            ed25519_simd_check_8_torsion_ifma(
                core::ptr::from_ref(self).cast(),
                core::ptr::from_ref(rhs).cast(),
            )
        };
        mask_to_lanes(mask)
    }

    pub(super) fn negate(&self) -> Self {
        Self {
            x: self.x.negate(),
            y: self.y,
            z: self.z,
            t: self.t.negate(),
        }
    }

    /// Return whether each point is killed by the Ed25519 cofactor.
    pub(super) fn is_small_order_lanes(&self) -> [bool; LANES] {
        #[cfg(debug_assertions)]
        for field in [&self.x, &self.y] {
            debug_assert!(limbs_are_ifma_operands(&field.limbs));
        }
        // SAFETY: WidePoint's repr(C) layout places X and Y first. Both
        // the decoder and the ladder supply five 52-bit limbs per field.
        let mask = unsafe { ed25519_simd_small_order_ifma(core::ptr::from_ref(self).cast()) };
        mask_to_lanes(mask)
    }

    /// In place so `acc = acc.double_four_times()`'s 1280-byte return
    /// copy never happens; the last double writes straight into `self`.
    #[inline(never)]
    pub(super) fn double_four_times_assign(&mut self) {
        unsafe {
            // The ladder's cached-point recovery and strict products satisfy
            // the input bounds. `self` supplies exclusive access and layout.
            ed25519_simd_double4_ifma(core::ptr::from_mut(self).cast());
        }
    }

    pub(super) fn compress(&self) -> [[u8; POINT_ENCODING_LEN]; LANES] {
        let zinv = self.z.invert();
        let x = self.x.multiply(&zinv);
        let y = self.y.multiply(&zinv);
        let x_odd_mask = x.is_odd_mask();
        let mut bytes = y.to_bytes_lanes();
        for (lane, encoding) in bytes.iter_mut().enumerate() {
            encoding[31] |= ((x_odd_mask >> lane) & 1) << 7;
        }
        bytes
    }
}
