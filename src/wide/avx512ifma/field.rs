use super::{LANES, mask_to_lanes};
use crate::edwards::POINT_ENCODING_LEN;
use crate::field::{Fe51, LIMB_COUNT};
use std::arch::x86_64::*;

const LIMB_MASK: u64 = (1u64 << 51) - 1;

#[derive(Clone, Copy)]
pub(super) struct WideFe {
    pub(super) limbs: [__m512i; LIMB_COUNT],
}

#[derive(Clone, Copy)]
pub(super) struct WideFePair(WideFe, WideFe);

trait PowChainValue: Copy {
    fn chain_square(self) -> Self;
    fn chain_square_repeat<const N: usize>(self) -> Self;
    fn chain_multiply(self, rhs: Self) -> Self;
}

/// The `(p-5)/8` addition chain, shared by both the single-value and
/// latency-interleaved pair implementations.
#[inline(always)]
fn pow_p_minus_5_over_8_chain<T: PowChainValue>(z: T) -> T {
    let t0 = z.chain_square();
    let t1 = t0.chain_square_repeat::<2>().chain_multiply(z);
    let t0 = t0.chain_multiply(t1);
    let t0 = t0.chain_square().chain_multiply(t1);
    let t1 = t0.chain_square_repeat::<5>();
    let t0 = t1.chain_multiply(t0);
    let t1 = t0.chain_square_repeat::<10>().chain_multiply(t0);
    let t2 = t1.chain_square_repeat::<20>();
    let t1 = t2.chain_multiply(t1);
    let t1 = t1.chain_square_repeat::<10>();
    let t0 = t1.chain_multiply(t0);
    let t1 = t0.chain_square_repeat::<50>().chain_multiply(t0);
    let t2 = t1.chain_square_repeat::<100>();
    let t1 = t2.chain_multiply(t1);
    let t1 = t1.chain_square_repeat::<50>();
    let t0 = t1.chain_multiply(t0);
    t0.chain_square_repeat::<2>().chain_multiply(z)
}
impl WideFe {
    pub(super) fn zero() -> Self {
        unsafe {
            let z = _mm512_setzero_si512();
            Self {
                limbs: [z; LIMB_COUNT],
            }
        }
    }
    pub(super) fn one() -> Self {
        unsafe {
            let z = _mm512_setzero_si512();
            Self {
                limbs: [_mm512_set1_epi64(1), z, z, z, z],
            }
        }
    }
    /// Transpose eight lanes of scalar limbs. Inlined so both entry points
    /// below cost the same as an open-coded loop.
    #[inline(always)]
    pub(super) fn from_limbs_per_lane(limbs_of: impl Fn(usize) -> [u64; LIMB_COUNT]) -> Self {
        let mut by_limb = [[0u64; LANES]; LIMB_COUNT];
        let mut lane = 0;
        while lane < LANES {
            let limbs = limbs_of(lane);
            let mut limb = 0;
            while limb < LIMB_COUNT {
                by_limb[limb][lane] = limbs[limb];
                limb += 1;
            }
            lane += 1;
        }

        Self {
            limbs: [
                loadu(by_limb[0]),
                loadu(by_limb[1]),
                loadu(by_limb[2]),
                loadu(by_limb[3]),
                loadu(by_limb[4]),
            ],
        }
    }
    pub(super) fn from_fields(fields: &[Fe51; LANES]) -> Self {
        Self::from_limbs_per_lane(|lane| fields[lane].loose_limbs())
    }
    pub(super) fn from_field_refs(fields: &[&Fe51; LANES]) -> Self {
        Self::from_limbs_per_lane(|lane| fields[lane].loose_limbs())
    }
    pub(super) fn lane0(self) -> Fe51 {
        unsafe {
            Fe51::from_limbs_unchecked(core::array::from_fn(|i| {
                _mm_cvtsi128_si64(_mm512_castsi512_si128(self.limbs[i])) as u64
            }))
        }
    }
    /// Like `to_fields` but stores loosely-reduced limbs (no canonicalize);
    /// valid because a reduce leaves each limb `< 2^52`.
    pub(super) fn to_fields_loose(self) -> [Fe51; LANES] {
        let mut by_limb = [[0u64; LANES]; LIMB_COUNT];
        storeu(self.limbs[0], &mut by_limb[0]);
        storeu(self.limbs[1], &mut by_limb[1]);
        storeu(self.limbs[2], &mut by_limb[2]);
        storeu(self.limbs[3], &mut by_limb[3]);
        storeu(self.limbs[4], &mut by_limb[4]);

        core::array::from_fn(|lane| {
            Fe51::from_limbs_unchecked([
                by_limb[0][lane],
                by_limb[1][lane],
                by_limb[2][lane],
                by_limb[3][lane],
                by_limb[4][lane],
            ])
        })
    }
    pub(super) fn to_bytes_lanes(self) -> [[u8; POINT_ENCODING_LEN]; LANES] {
        unsafe {
            let c = self.canonical();
            // Packing overlaps unless canonical limb 0 is below 2^51.
            debug_assert!(
                c.limb_below(0, 51),
                "to_bytes_lanes needs a canonical limb 0 below 2^51"
            );
            let packed = [
                _mm512_or_si512(c.limbs[0], _mm512_slli_epi64(c.limbs[1], 51)),
                _mm512_or_si512(
                    _mm512_srli_epi64(c.limbs[1], 13),
                    _mm512_slli_epi64(c.limbs[2], 38),
                ),
                _mm512_or_si512(
                    _mm512_srli_epi64(c.limbs[2], 26),
                    _mm512_slli_epi64(c.limbs[3], 25),
                ),
                _mm512_or_si512(
                    _mm512_srli_epi64(c.limbs[3], 39),
                    _mm512_slli_epi64(c.limbs[4], 12),
                ),
            ];
            let mut words = [[0u64; LANES]; 4];
            storeu(packed[0], &mut words[0]);
            storeu(packed[1], &mut words[1]);
            storeu(packed[2], &mut words[2]);
            storeu(packed[3], &mut words[3]);

            core::array::from_fn(|lane| {
                let mut bytes = [0u8; POINT_ENCODING_LEN];
                let mut word = 0;
                while word < 4 {
                    bytes[word * 8..word * 8 + 8].copy_from_slice(&words[word][lane].to_le_bytes());
                    word += 1;
                }
                bytes
            })
        }
    }
    // Full reduction keeps results strict enough for small-bias subtracts.
    pub(super) fn add(&self, rhs: &Self) -> Self {
        unsafe {
            let h = [
                _mm512_add_epi64(self.limbs[0], rhs.limbs[0]),
                _mm512_add_epi64(self.limbs[1], rhs.limbs[1]),
                _mm512_add_epi64(self.limbs[2], rhs.limbs[2]),
                _mm512_add_epi64(self.limbs[3], rhs.limbs[3]),
                _mm512_add_epi64(self.limbs[4], rhs.limbs[4]),
            ];
            let reduced = Self::reduce_loose(h);
            Self::carry_limb0(reduced.limbs)
        }
    }
    pub(super) fn add_loose(&self, rhs: &Self) -> Self {
        unsafe {
            let h = [
                _mm512_add_epi64(self.limbs[0], rhs.limbs[0]),
                _mm512_add_epi64(self.limbs[1], rhs.limbs[1]),
                _mm512_add_epi64(self.limbs[2], rhs.limbs[2]),
                _mm512_add_epi64(self.limbs[3], rhs.limbs[3]),
                _mm512_add_epi64(self.limbs[4], rhs.limbs[4]),
            ];
            Self::reduce_loose(h)
        }
    }
    // The 4*p bias is only enough for strict subtrahends (`< 2^52` limbs);
    // loose limb0 can reach < 2^60, so those callers use `subtract_loose`.
    //
    // Note the suffix convention split: on `multiply`/`square`/`add`,
    // `_loose` marks a looser *result*; on the subtraction family below it
    // marks looser *operands* (the results are equally loose either way).
    pub(super) fn subtract(&self, rhs: &Self) -> Self {
        unsafe {
            let bias = [
                _mm512_set1_epi64(((4 * LIMB_MASK) - 18 * 4) as i64),
                _mm512_set1_epi64((4 * LIMB_MASK) as i64),
                _mm512_set1_epi64((4 * LIMB_MASK) as i64),
                _mm512_set1_epi64((4 * LIMB_MASK) as i64),
                _mm512_set1_epi64((4 * LIMB_MASK) as i64),
            ];
            let h = [
                _mm512_sub_epi64(_mm512_add_epi64(self.limbs[0], bias[0]), rhs.limbs[0]),
                _mm512_sub_epi64(_mm512_add_epi64(self.limbs[1], bias[1]), rhs.limbs[1]),
                _mm512_sub_epi64(_mm512_add_epi64(self.limbs[2], bias[2]), rhs.limbs[2]),
                _mm512_sub_epi64(_mm512_add_epi64(self.limbs[3], bias[3]), rhs.limbs[3]),
                _mm512_sub_epi64(_mm512_add_epi64(self.limbs[4], bias[4]), rhs.limbs[4]),
            ];
            Self::reduce_loose(h)
        }
    }
    pub(super) fn square_accum(&self) -> ([__m512i; LIMB_COUNT], [__m512i; LIMB_COUNT]) {
        unsafe {
            let z = _mm512_setzero_si512();
            let mut lo = [z; LIMB_COUNT];
            let mut hi = [z; LIMB_COUNT];

            // Carry only loose limb0. The remaining limbs may be just over
            // 51 bits, but are still valid IFMA52 inputs. Cross-products
            // are doubled in their accumulators instead of doubling an
            // input and forcing a full carry chain.
            let limbs = {
                let mask = _mm512_set1_epi64(LIMB_MASK as i64);
                let mut l = self.limbs;
                let carry = _mm512_srli_epi64(l[0], 51);
                l[0] = _mm512_and_si512(l[0], mask);
                l[1] = _mm512_add_epi64(l[1], carry);
                l
            };

            madd_one(&mut lo[0], &mut hi[0], limbs[0], limbs[0]);
            let (mut wlo, mut whi) = (z, z);
            madd_one(&mut wlo, &mut whi, limbs[1], limbs[4]);
            madd_one(&mut wlo, &mut whi, limbs[2], limbs[3]);
            double_accum(&mut wlo, &mut whi);
            add_wrap19(&mut lo[0], &mut hi[0], wlo, whi);

            madd_one(&mut lo[1], &mut hi[1], limbs[0], limbs[1]);
            double_accum(&mut lo[1], &mut hi[1]);
            let (mut wlo, mut whi) = (z, z);
            madd_one(&mut wlo, &mut whi, limbs[2], limbs[4]);
            double_accum(&mut wlo, &mut whi);
            madd_one(&mut wlo, &mut whi, limbs[3], limbs[3]);
            add_wrap19(&mut lo[1], &mut hi[1], wlo, whi);

            madd_one(&mut lo[2], &mut hi[2], limbs[0], limbs[2]);
            double_accum(&mut lo[2], &mut hi[2]);
            madd_one(&mut lo[2], &mut hi[2], limbs[1], limbs[1]);
            let (mut wlo, mut whi) = (z, z);
            madd_one(&mut wlo, &mut whi, limbs[3], limbs[4]);
            double_accum(&mut wlo, &mut whi);
            add_wrap19(&mut lo[2], &mut hi[2], wlo, whi);

            madd_one(&mut lo[3], &mut hi[3], limbs[0], limbs[3]);
            madd_one(&mut lo[3], &mut hi[3], limbs[1], limbs[2]);
            double_accum(&mut lo[3], &mut hi[3]);
            let (mut wlo, mut whi) = (z, z);
            madd_one(&mut wlo, &mut whi, limbs[4], limbs[4]);
            add_wrap19(&mut lo[3], &mut hi[3], wlo, whi);

            madd_one(&mut lo[4], &mut hi[4], limbs[0], limbs[4]);
            madd_one(&mut lo[4], &mut hi[4], limbs[1], limbs[3]);
            double_accum(&mut lo[4], &mut hi[4]);
            madd_one(&mut lo[4], &mut hi[4], limbs[2], limbs[2]);

            (lo, hi)
        }
    }
    pub(super) fn square_loose(&self) -> Self {
        let (lo, hi) = self.square_accum();
        Self::reduce_ifma_loose(lo, hi)
    }
    // Strict and loose multiplication differ only in final reduction.
    pub(super) fn multiply_accum(
        &self,
        rhs: &Self,
    ) -> ([__m512i; LIMB_COUNT], [__m512i; LIMB_COUNT]) {
        unsafe {
            let z = _mm512_setzero_si512();
            let mut lo = [z; LIMB_COUNT];
            let mut hi = [z; LIMB_COUNT];

            madd_one(&mut lo[0], &mut hi[0], self.limbs[0], rhs.limbs[0]);
            let (mut wlo, mut whi) = (z, z);
            madd_one(&mut wlo, &mut whi, self.limbs[1], rhs.limbs[4]);
            madd_one(&mut wlo, &mut whi, self.limbs[2], rhs.limbs[3]);
            madd_one(&mut wlo, &mut whi, self.limbs[3], rhs.limbs[2]);
            madd_one(&mut wlo, &mut whi, self.limbs[4], rhs.limbs[1]);
            add_wrap19(&mut lo[0], &mut hi[0], wlo, whi);

            madd_one(&mut lo[1], &mut hi[1], self.limbs[0], rhs.limbs[1]);
            madd_one(&mut lo[1], &mut hi[1], self.limbs[1], rhs.limbs[0]);
            let (mut wlo, mut whi) = (z, z);
            madd_one(&mut wlo, &mut whi, self.limbs[2], rhs.limbs[4]);
            madd_one(&mut wlo, &mut whi, self.limbs[3], rhs.limbs[3]);
            madd_one(&mut wlo, &mut whi, self.limbs[4], rhs.limbs[2]);
            add_wrap19(&mut lo[1], &mut hi[1], wlo, whi);

            madd_one(&mut lo[2], &mut hi[2], self.limbs[0], rhs.limbs[2]);
            madd_one(&mut lo[2], &mut hi[2], self.limbs[1], rhs.limbs[1]);
            madd_one(&mut lo[2], &mut hi[2], self.limbs[2], rhs.limbs[0]);
            let (mut wlo, mut whi) = (z, z);
            madd_one(&mut wlo, &mut whi, self.limbs[3], rhs.limbs[4]);
            madd_one(&mut wlo, &mut whi, self.limbs[4], rhs.limbs[3]);
            add_wrap19(&mut lo[2], &mut hi[2], wlo, whi);

            madd_one(&mut lo[3], &mut hi[3], self.limbs[0], rhs.limbs[3]);
            madd_one(&mut lo[3], &mut hi[3], self.limbs[1], rhs.limbs[2]);
            madd_one(&mut lo[3], &mut hi[3], self.limbs[2], rhs.limbs[1]);
            madd_one(&mut lo[3], &mut hi[3], self.limbs[3], rhs.limbs[0]);
            let (mut wlo, mut whi) = (z, z);
            madd_one(&mut wlo, &mut whi, self.limbs[4], rhs.limbs[4]);
            add_wrap19(&mut lo[3], &mut hi[3], wlo, whi);

            madd_one(&mut lo[4], &mut hi[4], self.limbs[0], rhs.limbs[4]);
            madd_one(&mut lo[4], &mut hi[4], self.limbs[1], rhs.limbs[3]);
            madd_one(&mut lo[4], &mut hi[4], self.limbs[2], rhs.limbs[2]);
            madd_one(&mut lo[4], &mut hi[4], self.limbs[3], rhs.limbs[1]);
            madd_one(&mut lo[4], &mut hi[4], self.limbs[4], rhs.limbs[0]);

            (lo, hi)
        }
    }
    pub(super) fn multiply_loose(&self, rhs: &Self) -> Self {
        let (lo, hi) = self.multiply_accum(rhs);
        Self::reduce_ifma_loose(lo, hi)
    }

    // One IFMA carry pass leaves limb0 < 2^60 and limbs 1..4 < 2^51.
    pub(super) fn reduce_ifma_loose(
        mut lo: [__m512i; LIMB_COUNT],
        hi: [__m512i; LIMB_COUNT],
    ) -> Self {
        unsafe {
            let mask = _mm512_set1_epi64(LIMB_MASK as i64);
            let nineteen = _mm512_set1_epi64(19);

            let mut i = 0;
            while i < 4 {
                let carry =
                    _mm512_add_epi64(_mm512_srli_epi64(lo[i], 51), _mm512_slli_epi64(hi[i], 1));
                lo[i] = _mm512_and_si512(lo[i], mask);
                lo[i + 1] = _mm512_add_epi64(lo[i + 1], carry);
                i += 1;
            }

            let carry = _mm512_add_epi64(_mm512_srli_epi64(lo[4], 51), _mm512_slli_epi64(hi[4], 1));
            lo[4] = _mm512_and_si512(lo[4], mask);
            lo[0] = _mm512_add_epi64(lo[0], _mm512_mullo_epi64(carry, nineteen));

            Self { limbs: lo }
        }
    }

    // `self + 2048*p - rhs`. These loose-input forms use a 2048*p bias,
    // enough for two loose subtrahends (limb0 < 2^60); `subtract`'s 4*p is not.
    pub(super) fn subtract_loose(&self, rhs: &Self) -> Self {
        unsafe {
            let b0 = _mm512_set1_epi64((2048 * (LIMB_MASK - 18)) as i64);
            let bn = _mm512_set1_epi64((2048 * LIMB_MASK) as i64);
            let h = [
                _mm512_sub_epi64(_mm512_add_epi64(self.limbs[0], b0), rhs.limbs[0]),
                _mm512_sub_epi64(_mm512_add_epi64(self.limbs[1], bn), rhs.limbs[1]),
                _mm512_sub_epi64(_mm512_add_epi64(self.limbs[2], bn), rhs.limbs[2]),
                _mm512_sub_epi64(_mm512_add_epi64(self.limbs[3], bn), rhs.limbs[3]),
                _mm512_sub_epi64(_mm512_add_epi64(self.limbs[4], bn), rhs.limbs[4]),
            ];
            Self::reduce_loose(h)
        }
    }

    // `self + 2048*p - lhs - rhs`, with all three possibly loose.
    pub(super) fn subtract_loose_sum(&self, lhs: &Self, rhs: &Self) -> Self {
        unsafe {
            let b0 = _mm512_set1_epi64((2048 * (LIMB_MASK - 18)) as i64);
            let bn = _mm512_set1_epi64((2048 * LIMB_MASK) as i64);
            let bias = [b0, bn, bn, bn, bn];
            let h = core::array::from_fn(|i| {
                _mm512_sub_epi64(
                    _mm512_sub_epi64(_mm512_add_epi64(self.limbs[i], bias[i]), lhs.limbs[i]),
                    rhs.limbs[i],
                )
            });
            Self::reduce_loose(h)
        }
    }

    // Fold `2*rhs` into the loose-input subtraction to avoid a carry pass.
    pub(super) fn subtract_loose_sum_with_doubled_rhs(&self, lhs: &Self, rhs: &Self) -> Self {
        unsafe {
            let b0 = _mm512_set1_epi64((2048 * (LIMB_MASK - 18)) as i64);
            let bn = _mm512_set1_epi64((2048 * LIMB_MASK) as i64);
            let bias = [b0, bn, bn, bn, bn];
            let h = core::array::from_fn(|i| {
                _mm512_sub_epi64(
                    _mm512_sub_epi64(_mm512_add_epi64(self.limbs[i], bias[i]), lhs.limbs[i]),
                    _mm512_slli_epi64(rhs.limbs[i], 1),
                )
            });
            Self::reduce_loose(h)
        }
    }

    // `2048*p - lhs - rhs`, with `lhs`/`rhs` possibly loose.
    pub(super) fn negate_loose_sum(lhs: &Self, rhs: &Self) -> Self {
        unsafe {
            let b0 = _mm512_set1_epi64((2048 * (LIMB_MASK - 18)) as i64);
            let bn = _mm512_set1_epi64((2048 * LIMB_MASK) as i64);
            let bias = [b0, bn, bn, bn, bn];
            let h = core::array::from_fn(|i| {
                _mm512_sub_epi64(_mm512_sub_epi64(bias[i], lhs.limbs[i]), rhs.limbs[i])
            });
            Self::reduce_loose(h)
        }
    }
    pub(super) fn negate(&self) -> Self {
        Self::zero().subtract(self)
    }
    pub(super) fn double(&self) -> Self {
        self.add(self)
    }
    pub(super) fn double_loose(&self) -> Self {
        self.add_loose(self)
    }
    pub(super) fn square(&self) -> Self {
        let (lo, hi) = self.square_accum();
        Self::reduce_ifma(lo, hi)
    }
    pub(super) fn multiply(&self, rhs: &Self) -> Self {
        let (lo, hi) = self.multiply_accum(rhs);
        Self::reduce_ifma(lo, hi)
    }
    pub(super) fn pow_p_minus_5_over_8(&self) -> Self {
        pow_p_minus_5_over_8_chain(*self)
    }

    /// Initialization-only copy. The out-of-line wrapper keeps setup call
    /// sites from perturbing the hot path's inlining.
    #[inline(never)]
    pub(super) fn cold_pow_p_minus_5_over_8(&self) -> Self {
        pow_p_minus_5_over_8_chain(*self)
    }

    /// The inversion addition chain, shared by both entry points.
    #[inline(always)]
    pub(super) fn invert_chain(&self) -> Self {
        let z = self;
        let t0 = z.square();
        let t1 = t0.square_repeat::<2>().multiply(z);
        let z11 = t0.multiply(&t1);
        let a = z11.square().multiply(&t1);
        let b = a.square_repeat::<5>().multiply(&a);
        let c = b.square_repeat::<10>().multiply(&b);
        let d = c.square_repeat::<20>().multiply(&c);
        let e = d.square_repeat::<10>().multiply(&b);
        let f = e.square_repeat::<50>().multiply(&e);
        let g = f.square_repeat::<100>().multiply(&f);
        let h = g.square_repeat::<50>().multiply(&e);
        h.square_repeat::<5>().multiply(&z11)
    }
    pub(super) fn invert(&self) -> Self {
        self.invert_chain()
    }

    /// Initialization-only copy; see [`cold_pow_p_minus_5_over_8`](Self::cold_pow_p_minus_5_over_8).
    #[inline(never)]
    pub(super) fn cold_invert(&self) -> Self {
        self.invert_chain()
    }
    // Keep intermediates loose; reduce only the final result for multiplication.
    pub(super) fn square_repeat<const N: usize>(&self) -> Self {
        let mut out = *self;
        for i in 0..N {
            out = if i + 1 < N {
                out.square_loose()
            } else {
                out.square()
            };
        }
        out
    }

    // Interleave two exponentiation chains to hide IFMA latency.
    pub(super) fn square_repeat_x2<const N: usize>(a: &Self, b: &Self) -> (Self, Self) {
        let (mut x, mut y) = (*a, *b);
        for i in 0..N {
            if i + 1 < N {
                x = x.square_loose();
                y = y.square_loose();
            } else {
                x = x.square();
                y = y.square();
            }
        }
        (x, y)
    }

    pub(super) fn pow_p_minus_5_over_8_x2(a: &Self, b: &Self) -> (Self, Self) {
        let pair = pow_p_minus_5_over_8_chain(WideFePair(*a, *b));
        (pair.0, pair.1)
    }
    pub(super) fn equals_lanes(self, rhs: &Self) -> [bool; LANES] {
        mask_to_lanes(self.equals_mask(rhs))
    }
    pub(super) fn equals_mask(self, rhs: &Self) -> u8 {
        self.subtract(rhs).is_zero_mask()
    }
    pub(super) fn is_zero_lanes(self) -> [bool; LANES] {
        mask_to_lanes(self.is_zero_mask())
    }
    pub(super) fn is_zero_mask(self) -> u8 {
        self.canonical().canonical_zero_mask()
    }
    /// Zero mask of an already-canonicalized value.
    #[inline(always)]
    pub(super) fn canonical_zero_mask(&self) -> u8 {
        unsafe {
            let zero = _mm512_setzero_si512();
            _mm512_cmpeq_epu64_mask(self.limbs[0], zero)
                & _mm512_cmpeq_epu64_mask(self.limbs[1], zero)
                & _mm512_cmpeq_epu64_mask(self.limbs[2], zero)
                & _mm512_cmpeq_epu64_mask(self.limbs[3], zero)
                & _mm512_cmpeq_epu64_mask(self.limbs[4], zero)
        }
    }
    #[cfg(test)]
    pub(super) fn is_odd_lanes(self) -> [bool; LANES] {
        mask_to_lanes(self.is_odd_mask())
    }
    pub(super) fn limb_below(&self, index: usize, bits: u32) -> bool {
        let mut lanes = [0u64; LANES];
        storeu(self.limbs[index], &mut lanes);
        lanes.iter().all(|&limb| limb < (1u64 << bits))
    }

    pub(super) fn is_odd_mask(self) -> u8 {
        unsafe {
            let c = self.canonical();
            let one = _mm512_set1_epi64(1);
            _mm512_test_epi64_mask(c.limbs[0], one)
        }
    }
    /// Return parity and zero masks from one canonicalization.
    pub(super) fn odd_and_zero_masks(self) -> (u8, u8) {
        unsafe {
            let c = self.canonical();
            let one = _mm512_set1_epi64(1);
            (
                _mm512_test_epi64_mask(c.limbs[0], one),
                c.canonical_zero_mask(),
            )
        }
    }
    /// Vectorized `Fe51::canonical`; bounded high limbs reduce `>= p` to a
    /// high-limb check and limb-0 threshold.
    pub(super) fn canonical(&self) -> Self {
        unsafe {
            let reduced = Self::carry_reduce_twice(self.limbs);
            let mask = _mm512_set1_epi64(LIMB_MASK as i64);
            let p0 = _mm512_set1_epi64((LIMB_MASK - 18) as i64);

            let ge_high = _mm512_cmpeq_epu64_mask(reduced.limbs[1], mask)
                & _mm512_cmpeq_epu64_mask(reduced.limbs[2], mask)
                & _mm512_cmpeq_epu64_mask(reduced.limbs[3], mask)
                & _mm512_cmpeq_epu64_mask(reduced.limbs[4], mask);
            let ge_p = ge_high & _mm512_cmpge_epu64_mask(reduced.limbs[0], p0);

            let zero = _mm512_setzero_si512();
            let sub0 = _mm512_sub_epi64(reduced.limbs[0], p0);
            Self {
                limbs: [
                    _mm512_mask_blend_epi64(ge_p, reduced.limbs[0], sub0),
                    _mm512_mask_blend_epi64(ge_p, reduced.limbs[1], zero),
                    _mm512_mask_blend_epi64(ge_p, reduced.limbs[2], zero),
                    _mm512_mask_blend_epi64(ge_p, reduced.limbs[3], zero),
                    _mm512_mask_blend_epi64(ge_p, reduced.limbs[4], zero),
                ],
            }
        }
    }
    pub(super) fn blend(&self, mask: u8, rhs: &Self) -> Self {
        unsafe {
            let mask = mask as __mmask8;
            Self {
                limbs: [
                    _mm512_mask_blend_epi64(mask, self.limbs[0], rhs.limbs[0]),
                    _mm512_mask_blend_epi64(mask, self.limbs[1], rhs.limbs[1]),
                    _mm512_mask_blend_epi64(mask, self.limbs[2], rhs.limbs[2]),
                    _mm512_mask_blend_epi64(mask, self.limbs[3], rhs.limbs[3]),
                    _mm512_mask_blend_epi64(mask, self.limbs[4], rhs.limbs[4]),
                ],
            }
        }
    }
    pub(super) fn reduce_ifma(lo: [__m512i; LIMB_COUNT], hi: [__m512i; LIMB_COUNT]) -> Self {
        // Only limb 0 retains a residual; carry it to restore IFMA bounds.
        Self::carry_limb0(Self::reduce_ifma_loose(lo, hi).limbs)
    }
    /// Carry loose limb 0, restoring the `< 2^52` IFMA input bound.
    pub(super) fn carry_limb0(mut h: [__m512i; LIMB_COUNT]) -> Self {
        unsafe {
            let mask = _mm512_set1_epi64(LIMB_MASK as i64);
            let carry = _mm512_srli_epi64(h[0], 51);
            h[0] = _mm512_and_si512(h[0], mask);
            h[1] = _mm512_add_epi64(h[1], carry);
            Self { limbs: h }
        }
    }
    /// One carry pass: limbs 1..4 become `< 2^51`; limb 0 may keep the
    /// small wraparound residual needed by additive consumers.
    pub(super) fn reduce_loose(mut h: [__m512i; LIMB_COUNT]) -> Self {
        unsafe {
            let mask = _mm512_set1_epi64(LIMB_MASK as i64);
            let nineteen = _mm512_set1_epi64(19);

            let mut i = 0;
            while i < 4 {
                let carry = _mm512_srli_epi64(h[i], 51);
                h[i] = _mm512_and_si512(h[i], mask);
                h[i + 1] = _mm512_add_epi64(h[i + 1], carry);
                i += 1;
            }

            let carry = _mm512_srli_epi64(h[4], 51);
            h[4] = _mm512_and_si512(h[4], mask);
            h[0] = _mm512_add_epi64(h[0], _mm512_mullo_epi64(carry, nineteen));

            Self { limbs: h }
        }
    }
    /// Two carry passes, used when `add`/`canonical` need near-strict limbs.
    pub(super) fn carry_reduce_twice(h: [__m512i; LIMB_COUNT]) -> Self {
        Self::reduce_loose(Self::reduce_loose(h).limbs)
    }
}
impl WideFe {
    pub(super) fn constant(limbs: [u64; LIMB_COUNT]) -> Self {
        unsafe {
            Self {
                limbs: [
                    _mm512_set1_epi64(limbs[0] as i64),
                    _mm512_set1_epi64(limbs[1] as i64),
                    _mm512_set1_epi64(limbs[2] as i64),
                    _mm512_set1_epi64(limbs[3] as i64),
                    _mm512_set1_epi64(limbs[4] as i64),
                ],
            }
        }
    }
    // Broadcast the shared scalar/SIMD constants from `field.rs`.
    pub(super) fn d() -> Self {
        Self::constant(crate::field::D_LIMBS)
    }
    pub(super) fn sqrt_m1() -> Self {
        Self::constant(crate::field::SQRT_M1_LIMBS)
    }
    pub(super) fn two_d() -> Self {
        Self::constant(crate::field::TWO_D_LIMBS)
    }
}
impl PowChainValue for WideFe {
    #[inline(always)]
    fn chain_square(self) -> Self {
        self.square()
    }

    #[inline(always)]
    fn chain_square_repeat<const N: usize>(self) -> Self {
        self.square_repeat::<N>()
    }

    #[inline(always)]
    fn chain_multiply(self, rhs: Self) -> Self {
        self.multiply(&rhs)
    }
}

impl PowChainValue for WideFePair {
    #[inline(always)]
    fn chain_square(self) -> Self {
        Self(self.0.square(), self.1.square())
    }

    #[inline(always)]
    fn chain_square_repeat<const N: usize>(self) -> Self {
        let (a, b) = WideFe::square_repeat_x2::<N>(&self.0, &self.1);
        Self(a, b)
    }

    #[inline(always)]
    fn chain_multiply(self, rhs: Self) -> Self {
        Self(self.0.multiply(&rhs.0), self.1.multiply(&rhs.1))
    }
}

fn madd_one(lo: &mut __m512i, hi: &mut __m512i, a: __m512i, b: __m512i) {
    unsafe {
        *lo = _mm512_madd52lo_epu64(*lo, a, b);
        *hi = _mm512_madd52hi_epu64(*hi, a, b);
    }
}
#[inline(always)]
fn double_accum(lo: &mut __m512i, hi: &mut __m512i) {
    unsafe {
        *lo = _mm512_add_epi64(*lo, *lo);
        *hi = _mm512_add_epi64(*hi, *hi);
    }
}
fn add_wrap19(lo: &mut __m512i, hi: &mut __m512i, wrap_lo: __m512i, wrap_hi: __m512i) {
    unsafe {
        let nineteen = _mm512_set1_epi64(19);
        *lo = _mm512_add_epi64(*lo, _mm512_mullo_epi64(wrap_lo, nineteen));
        *hi = _mm512_add_epi64(*hi, _mm512_mullo_epi64(wrap_hi, nineteen));
    }
}
pub(super) fn loadu(values: [u64; LANES]) -> __m512i {
    unsafe { _mm512_loadu_si512(values.as_ptr() as *const __m512i) }
}
pub(super) fn storeu(value: __m512i, out: &mut [u64; LANES]) {
    unsafe { _mm512_storeu_si512(out.as_mut_ptr() as *mut __m512i, value) }
}
