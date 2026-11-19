use super::LANES;
use super::point::WidePoint;
use crate::edwards::{AffineCachedPoint, CachedPoint};

#[cfg(all(feature = "asm", target_os = "linux", target_pointer_width = "64"))]
mod assembly {
    use super::*;
    use crate::field::Fe51;
    use crate::wide::avx512ifma::field::{WideFe, loadu};
    use core::arch::x86_64::*;

    core::arch::global_asm!(include_str!("ladder_step.S"), options(raw));

    // Transpose the first four limbs with 256-bit row loads. The fifth limb
    // uses scalar loads, so no field is read beyond its five initialized words.
    #[inline(always)]
    fn transpose_fields(fields: &[&Fe51; LANES]) -> WideFe {
        let rows = fields.map(|f| f.loose_limbs());
        // SAFETY: Each unaligned load reads four words from a five-word row.
        // Both halves use exactly four rows; the fifth words are read separately.
        // AVX-512F (and its AVX2 prerequisite) is required by the crate.
        unsafe {
            let half = |start: usize| {
                let a = _mm256_loadu_si256(rows[start].as_ptr().cast());
                let b = _mm256_loadu_si256(rows[start + 1].as_ptr().cast());
                let c = _mm256_loadu_si256(rows[start + 2].as_ptr().cast());
                let d = _mm256_loadu_si256(rows[start + 3].as_ptr().cast());
                let ab0 = _mm256_unpacklo_epi64(a, b);
                let ab1 = _mm256_unpackhi_epi64(a, b);
                let cd0 = _mm256_unpacklo_epi64(c, d);
                let cd1 = _mm256_unpackhi_epi64(c, d);
                [
                    _mm256_permute2x128_si256::<0x20>(ab0, cd0),
                    _mm256_permute2x128_si256::<0x20>(ab1, cd1),
                    _mm256_permute2x128_si256::<0x31>(ab0, cd0),
                    _mm256_permute2x128_si256::<0x31>(ab1, cd1),
                ]
            };
            let lo = half(0);
            let hi = half(4);
            WideFe {
                limbs: [
                    _mm512_inserti64x4::<1>(_mm512_castsi256_si512(lo[0]), hi[0]),
                    _mm512_inserti64x4::<1>(_mm512_castsi256_si512(lo[1]), hi[1]),
                    _mm512_inserti64x4::<1>(_mm512_castsi256_si512(lo[2]), hi[2]),
                    _mm512_inserti64x4::<1>(_mm512_castsi256_si512(lo[3]), hi[3]),
                    loadu(rows.map(|r| r[4])),
                ],
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::wide::avx512ifma::field::storeu;
        use rand::{RngCore, SeedableRng, rngs::StdRng};

        #[test]
        fn transpose_preserves_every_limb_and_lane() {
            let mut rng = StdRng::seed_from_u64(0x8f04_51a0);
            for case in 0..128 {
                let rows: [[u64; 5]; LANES] = core::array::from_fn(|lane| {
                    core::array::from_fn(|limb| match case {
                        0 => 0,
                        1 => (1 << 52) - 1,
                        2 => 1 << (lane * 5 + limb),
                        _ => rng.next_u64() & ((1 << 52) - 1),
                    })
                });
                let fields = rows.map(Fe51::from_limbs_unchecked);
                let actual = transpose_fields(&fields.each_ref());
                for limb in 0..5 {
                    let mut lanes = [0; LANES];
                    storeu(actual.limbs[limb], &mut lanes);
                    assert_eq!(lanes, core::array::from_fn(|lane| rows[lane][limb]));
                }
            }
        }
    }

    /// Cached coordinates in the order consumed by add_cached.S.
    #[repr(C)]
    struct StagedLadderStep {
        odd: [WideFe; 4],
        base: [WideFe; 3],
        even: [WideFe; 4],
    }

    const _: () = {
        use core::mem::{align_of, offset_of, size_of};
        assert!(align_of::<StagedLadderStep>() == 64);
        assert!(size_of::<StagedLadderStep>() == 3520);
        assert!(offset_of!(StagedLadderStep, odd) == 0);
        assert!(offset_of!(StagedLadderStep, base) == 1280);
        assert!(offset_of!(StagedLadderStep, even) == 2240);
    };

    impl StagedLadderStep {
        #[inline(always)]
        fn new(
            odd: &[&CachedPoint; LANES],
            base: &[&AffineCachedPoint; LANES],
            even: &[&CachedPoint; LANES],
        ) -> Self {
            #[inline(always)]
            fn projective(points: &[&CachedPoint; LANES]) -> [WideFe; 4] {
                [
                    transpose_fields(&points.map(|p| p.coords().1)),
                    transpose_fields(&points.map(|p| p.coords().0)),
                    transpose_fields(&points.map(|p| p.coords().3)),
                    transpose_fields(&points.map(|p| p.coords().2)),
                ]
            }
            Self {
                odd: projective(odd),
                base: [
                    transpose_fields(&base.map(|p| p.coords().1)),
                    transpose_fields(&base.map(|p| p.coords().0)),
                    transpose_fields(&base.map(|p| p.coords().2)),
                ],
                even: projective(even),
            }
        }
    }

    unsafe extern "C" {
        /// See ladder_step.S for bounds, layout, aliasing and stack requirements.
        /// The wrapper itself is not yet formally verified.
        fn ed25519_simd_ladder_step_ifma(point: *mut u8, operands: *const u8, compute_t: u64);
    }

    #[inline]
    pub(super) fn step(
        point: &mut WidePoint,
        odd: &[&CachedPoint; LANES],
        base: &[&AffineCachedPoint; LANES],
        even: &[&CachedPoint; LANES],
        compute_t: bool,
    ) {
        let operands = StagedLadderStep::new(odd, base, even);
        #[cfg(debug_assertions)]
        for field in operands
            .odd
            .iter()
            .chain(&operands.base)
            .chain(&operands.even)
        {
            debug_assert!(super::super::field::limbs_are_ifma_operands(&field.limbs));
        }
        // SAFETY: The accumulator satisfies the same loose XYZ bounds as the
        // existing double4 call. Selected table coordinates have 52-bit limbs.
        // The checked layouts provide aligned, initialized and disjoint storage;
        // compute_t is 0 or 1. Every intermediate output meets the next input's
        // bounds, and the first doubling ignores the incoming T coordinate.
        unsafe {
            ed25519_simd_ladder_step_ifma(
                core::ptr::from_mut(point).cast(),
                core::ptr::from_ref(&operands).cast(),
                u64::from(compute_t),
            );
        }
    }
}

impl WidePoint {
    /// Multiply by 256 and add the three already-selected signed multiples.
    /// `odd` is weighted by 16; `base` and `even` have weight one.
    #[inline]
    pub(super) fn ladder_step_assign(
        &mut self,
        odd: &[&CachedPoint; LANES],
        base: &[&AffineCachedPoint; LANES],
        even: &[&CachedPoint; LANES],
        compute_t: bool,
    ) {
        #[cfg(all(feature = "asm", target_os = "linux", target_pointer_width = "64"))]
        assembly::step(self, odd, base, even, compute_t);

        #[cfg(not(all(feature = "asm", target_os = "linux", target_pointer_width = "64")))]
        {
            self.double_four_times_assign();
            self.add_cached_refs_assign(odd, false);
            self.double_four_times_assign();
            self.add_affine_cached_refs_assign(base);
            self.add_cached_refs_assign(even, compute_t);
        }
    }
}
