const LIMB_BITS: usize = 51;
const MASK: u64 = (1u64 << LIMB_BITS) - 1;
// Number of 51-bit limbs needed to represent a value modulo p = 2^255 - 19.
pub(crate) const LIMB_COUNT: usize = 5;
const P_LIMBS: [u64; LIMB_COUNT] = [MASK - 18, MASK, MASK, MASK, MASK];

// Curve constants in 51-bit limbs. These are the single source of truth for both
// the scalar path here and the AVX-512 field in `wide.rs` (which broadcasts them
// into SIMD lanes via `WideFe::constant`), so the two paths can never drift.
pub(crate) const D_LIMBS: [u64; LIMB_COUNT] = [
    929_955_233_495_203,
    466_365_720_129_213,
    1_662_059_464_998_953,
    2_033_849_074_728_123,
    1_442_794_654_840_575,
];
pub(crate) const TWO_D_LIMBS: [u64; LIMB_COUNT] = [
    1_859_910_466_990_425,
    932_731_440_258_426,
    1_072_319_116_312_658,
    1_815_898_335_770_999,
    633_789_495_995_903,
];
pub(crate) const SQRT_M1_LIMBS: [u64; LIMB_COUNT] = [
    1_718_705_420_411_056,
    234_908_883_556_509,
    2_233_514_472_574_048,
    2_117_202_627_021_982,
    765_476_049_583_133,
];
#[cfg(test)]
const P_BYTES: [u8; 32] = [
    0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
];

#[derive(Clone, Copy, Debug)]
pub(crate) struct Fe51 {
    limbs: [u64; LIMB_COUNT],
}

impl Fe51 {
    pub(crate) fn from_limbs(limbs: [u64; LIMB_COUNT]) -> Self {
        Self { limbs }.canonical()
    }

    /// Store limbs without canonicalizing. Valid only when each limb is already
    /// `< 2^52` (the loosely-reduced invariant), e.g. straight from a wide reduce.
    pub(crate) fn from_limbs_unchecked(limbs: [u64; LIMB_COUNT]) -> Self {
        debug_assert!(limbs.iter().all(|&limb| limb < (1u64 << 52)));
        Self { limbs }
    }

    pub(crate) fn zero() -> Self {
        Self {
            limbs: [0; LIMB_COUNT],
        }
    }

    pub(crate) fn one() -> Self {
        Self {
            limbs: [1, 0, 0, 0, 0],
        }
    }

    pub(crate) fn d() -> Self {
        Self { limbs: D_LIMBS }
    }

    pub(crate) fn two_d() -> Self {
        Self { limbs: TWO_D_LIMBS }
    }

    fn sqrt_m1() -> Self {
        Self {
            limbs: SQRT_M1_LIMBS,
        }
    }

    // "Unchecked" means canonicality only; limb masking still yields `< 2^51`
    // limbs, safe for every field op here.
    pub(crate) fn from_bytes_unchecked(bytes: &[u8; 32]) -> Self {
        Self {
            limbs: [
                load_u64_le(bytes, 0) & MASK,
                (load_u64_le(bytes, 6) >> 3) & MASK,
                (load_u64_le(bytes, 12) >> 6) & MASK,
                (load_u64_le(bytes, 19) >> 1) & MASK,
                (load_u64_le(bytes, 24) >> 12) & MASK,
            ],
        }
    }

    pub(crate) fn to_bytes(self) -> [u8; 32] {
        let l = self.canonical().limbs;
        [
            l[0] as u8,
            (l[0] >> 8) as u8,
            (l[0] >> 16) as u8,
            (l[0] >> 24) as u8,
            (l[0] >> 32) as u8,
            (l[0] >> 40) as u8,
            ((l[0] >> 48) | (l[1] << 3)) as u8,
            (l[1] >> 5) as u8,
            (l[1] >> 13) as u8,
            (l[1] >> 21) as u8,
            (l[1] >> 29) as u8,
            (l[1] >> 37) as u8,
            ((l[1] >> 45) | (l[2] << 6)) as u8,
            (l[2] >> 2) as u8,
            (l[2] >> 10) as u8,
            (l[2] >> 18) as u8,
            (l[2] >> 26) as u8,
            (l[2] >> 34) as u8,
            (l[2] >> 42) as u8,
            ((l[2] >> 50) | (l[3] << 1)) as u8,
            (l[3] >> 7) as u8,
            (l[3] >> 15) as u8,
            (l[3] >> 23) as u8,
            (l[3] >> 31) as u8,
            (l[3] >> 39) as u8,
            ((l[3] >> 47) | (l[4] << 4)) as u8,
            (l[4] >> 4) as u8,
            (l[4] >> 12) as u8,
            (l[4] >> 20) as u8,
            (l[4] >> 28) as u8,
            (l[4] >> 36) as u8,
            (l[4] >> 44) as u8,
        ]
    }

    pub(crate) fn add(&self, rhs: &Self) -> Self {
        let mut h = [0u128; LIMB_COUNT];
        let mut i = 0;
        while i < LIMB_COUNT {
            h[i] = self.limbs[i] as u128 + rhs.limbs[i] as u128;
            i += 1;
        }
        Self::carry_reduce(h)
    }

    pub(crate) fn subtract(&self, rhs: &Self) -> Self {
        // Bias by 16*p so the limb-wise difference cannot underflow: operand
        // limbs are < 2^52 (the loosely-reduced invariant) while every bias
        // limb is >= 2^55 - 304, and the sums stay well below 2^64.
        const BIAS: [u64; LIMB_COUNT] =
            [16 * (MASK - 18), 16 * MASK, 16 * MASK, 16 * MASK, 16 * MASK];
        let mut h = [0u128; LIMB_COUNT];
        let mut i = 0;
        while i < LIMB_COUNT {
            h[i] = (self.limbs[i] + BIAS[i] - rhs.limbs[i]) as u128;
            i += 1;
        }
        Self::carry_reduce(h)
    }

    pub(crate) fn negate(&self) -> Self {
        Self::zero().subtract(self)
    }

    pub(crate) fn double(&self) -> Self {
        self.add(self)
    }

    pub(crate) fn multiply(&self, rhs: &Self) -> Self {
        let f0 = self.limbs[0] as u128;
        let f1 = self.limbs[1] as u128;
        let f2 = self.limbs[2] as u128;
        let f3 = self.limbs[3] as u128;
        let f4 = self.limbs[4] as u128;

        let g0 = rhs.limbs[0] as u128;
        let g1 = rhs.limbs[1] as u128;
        let g2 = rhs.limbs[2] as u128;
        let g3 = rhs.limbs[3] as u128;
        let g4 = rhs.limbs[4] as u128;

        let h0 = f0 * g0 + 19 * (f1 * g4 + f2 * g3 + f3 * g2 + f4 * g1);
        let h1 = f0 * g1 + f1 * g0 + 19 * (f2 * g4 + f3 * g3 + f4 * g2);
        let h2 = f0 * g2 + f1 * g1 + f2 * g0 + 19 * (f3 * g4 + f4 * g3);
        let h3 = f0 * g3 + f1 * g2 + f2 * g1 + f3 * g0 + 19 * (f4 * g4);
        let h4 = f0 * g4 + f1 * g3 + f2 * g2 + f3 * g1 + f4 * g0;

        Self::carry_reduce([h0, h1, h2, h3, h4])
    }

    pub(crate) fn square(&self) -> Self {
        let f0 = self.limbs[0] as u128;
        let f1 = self.limbs[1] as u128;
        let f2 = self.limbs[2] as u128;
        let f3 = self.limbs[3] as u128;
        let f4 = self.limbs[4] as u128;

        let h0 = f0 * f0 + 38 * (f1 * f4 + f2 * f3);
        let h1 = 2 * f0 * f1 + 38 * f2 * f4 + 19 * f3 * f3;
        let h2 = 2 * f0 * f2 + f1 * f1 + 38 * f3 * f4;
        let h3 = 2 * (f0 * f3 + f1 * f2) + 19 * f4 * f4;
        let h4 = 2 * (f0 * f4 + f1 * f3) + f2 * f2;

        Self::carry_reduce([h0, h1, h2, h3, h4])
    }

    pub(crate) fn sqrt_ratio(u: &Self, v: &Self) -> Option<Self> {
        let v2 = v.square();
        let v3 = v2.multiply(v);
        let v7 = v3.square().multiply(v);
        let x = u
            .multiply(&v3)
            .multiply(&u.multiply(&v7).pow_p_minus_5_over_8());

        // (sqrt(-1)*x)^2 * v == -(x^2 * v), so if the first candidate is off by
        // exactly a factor of -1, negating the already-computed `vx2` and
        // comparing to `u` decides it without recomputing `v * x^2`.
        let vx2 = v.multiply(&x.square());
        if vx2.equals(u) {
            Some(x)
        } else if vx2.negate().equals(u) {
            Some(x.multiply(&Self::sqrt_m1()))
        } else {
            None
        }
    }

    pub(crate) fn is_odd(&self) -> bool {
        (self.canonical().limbs[0] & 1) != 0
    }

    pub(crate) fn equals(&self, rhs: &Self) -> bool {
        self.canonical().limbs == rhs.canonical().limbs
    }

    /// Loosely reduced limbs for AVX-512 IFMA field arithmetic.
    #[allow(unused)]
    pub(crate) fn reduced_limbs(&self) -> [u64; LIMB_COUNT] {
        debug_assert!(self.limbs.iter().all(|&limb| limb < (1u64 << 52)));
        self.limbs
    }

    /// Loosely reduced limbs (`< 2^52`), borrowed for direct SIMD loads.
    pub(crate) fn limbs_ref(&self) -> &[u64; LIMB_COUNT] {
        debug_assert!(self.limbs.iter().all(|&limb| limb < (1u64 << 52)));
        &self.limbs
    }

    // Exposed to tests to cross-check the SIMD exponentiation chain.
    pub(crate) fn pow_p_minus_5_over_8(&self) -> Self {
        let t0 = self.square();
        let t1 = t0.square_repeat::<2>().multiply(self);
        let t0 = t0.multiply(&t1);
        let t0 = t0.square().multiply(&t1);
        let t1 = t0.square_repeat::<5>();
        let t0 = t1.multiply(&t0);
        let t1 = t0.square_repeat::<10>().multiply(&t0);
        let t2 = t1.square_repeat::<20>();
        let t1 = t2.multiply(&t1);
        let t1 = t1.square_repeat::<10>();
        let t0 = t1.multiply(&t0);
        let t1 = t0.square_repeat::<50>().multiply(&t0);
        let t2 = t1.square_repeat::<100>();
        let t1 = t2.multiply(&t1);
        let t1 = t1.square_repeat::<50>();
        let t0 = t1.multiply(&t0);
        t0.square_repeat::<2>().multiply(self)
    }

    #[inline(always)]
    fn square_repeat<const N: usize>(&self) -> Self {
        let mut out = *self;
        let mut i = 0;
        while i < N {
            out = out.square();
            i += 1;
        }
        out
    }

    // Shared carry prefix: limbs 0 and 2-4 are `< 2^51`; limb 1 may retain one
    // carry bit for callers to handle.
    fn carry_reduce_prefix(mut h: [u128; LIMB_COUNT]) -> [u128; LIMB_COUNT] {
        let mut i = 0;
        while i < LIMB_COUNT - 1 {
            let carry = h[i] >> LIMB_BITS;
            h[i] &= MASK as u128;
            h[i + 1] += carry;
            i += 1;
        }

        let carry = h[LIMB_COUNT - 1] >> LIMB_BITS;
        h[LIMB_COUNT - 1] &= MASK as u128;
        h[0] += carry * 19;

        let carry = h[0] >> LIMB_BITS;
        h[0] &= MASK as u128;
        h[1] += carry;

        h
    }

    fn pack_limbs(h: [u128; LIMB_COUNT]) -> Self {
        let mut limbs = [0u64; LIMB_COUNT];
        let mut i = 0;
        while i < LIMB_COUNT {
            limbs[i] = h[i] as u64;
            i += 1;
        }
        Self { limbs }
    }

    // Fast reduction used when limb 1's possible extra carry bit is acceptable.
    fn carry_reduce(h: [u128; LIMB_COUNT]) -> Self {
        Self::pack_limbs(Self::carry_reduce_prefix(h))
    }

    fn canonical(&self) -> Self {
        let mut h = [0u128; LIMB_COUNT];
        let mut i = 0;
        while i < LIMB_COUNT {
            h[i] = self.limbs[i] as u128;
            i += 1;
        }
        let mut fe = Self::carry_reduce_fully(h);
        if cmp_limbs(&fe.limbs, &P_LIMBS) != core::cmp::Ordering::Less {
            let mut out = [0u64; LIMB_COUNT];
            sub_limbs(&mut out, &fe.limbs, &P_LIMBS);
            fe.limbs = out;
        }
        fe
    }

    // Fully reduce every limb before comparing against `P_LIMBS`.
    fn carry_reduce_fully(h: [u128; LIMB_COUNT]) -> Self {
        let mut h = Self::carry_reduce_prefix(h);
        let carry = h[1] >> LIMB_BITS;
        h[1] &= MASK as u128;
        h[2] += carry;
        Self::pack_limbs(h)
    }

    #[cfg(test)]
    pub(crate) fn from_canonical_bytes(bytes: &[u8; 32]) -> Option<Self> {
        if !is_canonical_bytes(bytes) {
            return None;
        }
        Some(Self::from_bytes_unchecked(bytes))
    }

    pub(crate) fn invert(&self) -> Self {
        let mut exp = [0xffu8; 32];
        exp[0] = 0xeb;
        exp[31] = 0x7f;
        self.pow(&exp)
    }

    fn pow(&self, exp: &[u8; 32]) -> Self {
        let mut acc = Self::one();
        let mut i = 255;
        while i > 0 {
            i -= 1;
            acc = acc.square();
            if get_bit(exp, i) {
                acc = acc.multiply(self);
            }
        }
        acc
    }
}

#[cfg(test)]
fn is_canonical_bytes(bytes: &[u8; 32]) -> bool {
    let mut i = 32;
    while i > 0 {
        i -= 1;
        if bytes[i] < P_BYTES[i] {
            return true;
        }
        if bytes[i] > P_BYTES[i] {
            return false;
        }
    }
    false
}

fn load_u64_le(bytes: &[u8; 32], offset: usize) -> u64 {
    u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
}

fn get_bit(bytes: &[u8], bit: usize) -> bool {
    ((bytes[bit / 8] >> (bit % 8)) & 1) != 0
}

fn cmp_limbs(a: &[u64; LIMB_COUNT], b: &[u64; LIMB_COUNT]) -> core::cmp::Ordering {
    let mut i = 5;
    while i > 0 {
        i -= 1;
        match a[i].cmp(&b[i]) {
            core::cmp::Ordering::Equal => {}
            ord => return ord,
        }
    }
    core::cmp::Ordering::Equal
}

fn sub_limbs(out: &mut [u64; LIMB_COUNT], a: &[u64; LIMB_COUNT], b: &[u64; LIMB_COUNT]) {
    let mut borrow = 0i128;
    let base = 1i128 << LIMB_BITS;
    let mut i = 0;
    while i < LIMB_COUNT {
        let value = a[i] as i128 - b[i] as i128 - borrow;
        if value < 0 {
            out[i] = (value + base) as u64;
            borrow = 1;
        } else {
            out[i] = value as u64;
            borrow = 0;
        }
        i += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn square_matches_multiply_self() {
        let cases = [
            [0, 0, 0, 0, 0],
            [1, 0, 0, 0, 0],
            [MASK - 18, MASK, MASK, MASK, MASK - 1],
            [
                1_234_567_890_123,
                2_222_222_222_222,
                987_654_321_987,
                1_111_111_111_111,
                333_333_333_333,
            ],
        ];

        for limbs in cases {
            let x = Fe51::from_limbs(limbs);
            assert!(x.square().equals(&x.multiply(&x)));
        }
    }

    #[test]
    fn canonical_bytes_bound() {
        let mut p_minus_one = P_BYTES;
        p_minus_one[0] -= 1;
        assert!(Fe51::from_canonical_bytes(&p_minus_one).is_some());
        assert!(Fe51::from_canonical_bytes(&P_BYTES).is_none());

        let mut high_bit = [0u8; 32];
        high_bit[31] = 0x80;
        assert!(Fe51::from_canonical_bytes(&high_bit).is_none());
    }
}
