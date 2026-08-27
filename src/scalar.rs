const L_BYTES: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
];

pub(crate) type Radix16 = [i8; 64];

#[derive(Clone, Copy, Debug)]
pub(crate) struct Scalar {
    bytes: [u8; 32],
}

impl Scalar {
    pub(crate) fn from_canonical_bytes(bytes: [u8; 32]) -> Self {
        debug_assert!(is_canonical(&bytes));
        Self { bytes }
    }

    /// Reduce pre-swapped wide hash words, avoiding a byte round trip.
    pub(crate) fn from_wide_words(words: [u64; 8]) -> Self {
        Self {
            bytes: Scalar52::from_wide_words(&words).to_bytes(),
        }
    }

    pub(crate) fn to_radix16(self) -> Radix16 {
        // Adding 0x88..88 lets the binary carry chain produce balanced digits.
        let mut biased = [0u8; 32];
        let mut carry = 0u16;
        let mut i = 0;
        while i < 32 {
            let sum = self.bytes[i] as u16 + 0x88 + carry;
            biased[i] = sum as u8;
            carry = sum >> 8;
            i += 1;
        }
        // Scalars are reduced mod L < 2^253, so the top byte is < 0x20 and the
        // biased sum provably cannot carry out of 32 bytes.
        debug_assert_eq!(carry, 0, "radix-16 bias carried out of a reduced scalar");

        let mut digits = [0i8; 64];
        i = 0;
        while i < 32 {
            digits[2 * i] = (biased[i] & 0x0f) as i8 - 8;
            digits[2 * i + 1] = (biased[i] >> 4) as i8 - 8;
            i += 1;
        }
        digits
    }

    #[cfg(test)]
    pub(crate) fn to_radix16_carry_loop(self) -> Radix16 {
        let mut digits = [0i8; 64];
        let mut i = 0;
        while i < 32 {
            digits[2 * i] = (self.bytes[i] & 0x0f) as i8;
            digits[2 * i + 1] = (self.bytes[i] >> 4) as i8;
            i += 1;
        }
        let mut carry = 0i8;
        i = 0;
        while i < 64 {
            let digit = digits[i] + carry;
            if digit > 8 {
                digits[i] = digit - 16;
                carry = 1;
            } else {
                digits[i] = digit;
                carry = 0;
            }
            i += 1;
        }
        debug_assert_eq!(carry, 0);
        digits
    }

    /// Kept as a scalar reference for tests; the verifier's hot path uses
    /// `from_wide_words` to avoid the byte round trip this does internally.
    #[cfg(test)]
    pub(crate) fn from_wide_bytes(bytes: [u8; 64]) -> Self {
        Self {
            bytes: reduce_wide(bytes),
        }
    }
}

pub(crate) fn is_canonical(bytes: &[u8; 32]) -> bool {
    let mut i = 32;
    while i > 0 {
        i -= 1;
        if bytes[i] < L_BYTES[i] {
            return true;
        }
        if bytes[i] > L_BYTES[i] {
            return false;
        }
    }
    false
}

#[cfg(test)]
fn reduce_wide(bytes: [u8; 64]) -> [u8; 32] {
    Scalar52::from_wide_bytes(&bytes).to_bytes()
}

const LIMB52_MASK: u64 = (1u64 << 52) - 1;
// Number of 52-bit limbs needed to represent a value modulo L, the group order.
const LIMB_COUNT: usize = 5;
const SCALAR_L: Scalar52 = Scalar52([
    0x0002631a5cf5d3ed,
    0x000dea2f79cd6581,
    0x000000000014def9,
    0x0000000000000000,
    0x0000100000000000,
]);
const SCALAR_LFACTOR: u64 = 0x51da312547e1b;
const SCALAR_R: Scalar52 = Scalar52([
    0x000f48bd6721e6ed,
    0x0003bab5ac67e45a,
    0x000fffffeb35e51b,
    0x000fffffffffffff,
    0x00000fffffffffff,
]);
const SCALAR_RR: Scalar52 = Scalar52([
    0x0009d265e952d13b,
    0x000d63c715bea69f,
    0x0005be65cb687604,
    0x0003dceec73d217f,
    0x000009411b7c309a,
]);

#[derive(Clone, Copy)]
struct Scalar52([u64; LIMB_COUNT]);

impl Scalar52 {
    #[rustfmt::skip]
    fn from_wide_words(words: &[u64; 8]) -> Self {
        let lo = Scalar52([
              words[0]                              & LIMB52_MASK,
            ((words[0] >> 52) | (words[1] << 12))   & LIMB52_MASK,
            ((words[1] >> 40) | (words[2] << 24))   & LIMB52_MASK,
            ((words[2] >> 28) | (words[3] << 36))   & LIMB52_MASK,
            ((words[3] >> 16) | (words[4] << 48))   & LIMB52_MASK,
        ]);
        let hi = Scalar52([
             (words[4] >>  4)                       & LIMB52_MASK,
            ((words[4] >> 56) | (words[5] <<  8))   & LIMB52_MASK,
            ((words[5] >> 44) | (words[6] << 20))   & LIMB52_MASK,
            ((words[6] >> 32) | (words[7] << 32))   & LIMB52_MASK,
              words[7] >> 20,
        ]);

        Self::add(
            &hi.montgomery_mul(&SCALAR_RR),
            &lo.montgomery_mul(&SCALAR_R),
        )
    }

    #[rustfmt::skip]
    fn to_bytes(self) -> [u8; 32] {
        let limbs = self.0;
        [
              limbs[0]                             as u8,
             (limbs[0] >>  8)                      as u8,
             (limbs[0] >> 16)                      as u8,
             (limbs[0] >> 24)                      as u8,
             (limbs[0] >> 32)                      as u8,
             (limbs[0] >> 40)                      as u8,
            ((limbs[0] >> 48) | (limbs[1] << 4))   as u8,
             (limbs[1] >>  4)                      as u8,
             (limbs[1] >> 12)                      as u8,
             (limbs[1] >> 20)                      as u8,
             (limbs[1] >> 28)                      as u8,
             (limbs[1] >> 36)                      as u8,
             (limbs[1] >> 44)                      as u8,
              limbs[2]                             as u8,
             (limbs[2] >>  8)                      as u8,
             (limbs[2] >> 16)                      as u8,
             (limbs[2] >> 24)                      as u8,
             (limbs[2] >> 32)                      as u8,
             (limbs[2] >> 40)                      as u8,
            ((limbs[2] >> 48) | (limbs[3] << 4))   as u8,
             (limbs[3] >>  4)                      as u8,
             (limbs[3] >> 12)                      as u8,
             (limbs[3] >> 20)                      as u8,
             (limbs[3] >> 28)                      as u8,
             (limbs[3] >> 36)                      as u8,
             (limbs[3] >> 44)                      as u8,
              limbs[4]                             as u8,
             (limbs[4] >>  8)                      as u8,
             (limbs[4] >> 16)                      as u8,
             (limbs[4] >> 24)                      as u8,
             (limbs[4] >> 32)                      as u8,
             (limbs[4] >> 40)                      as u8,
        ]
    }

    fn add(a: &Self, b: &Self) -> Self {
        let mut out = [0u64; LIMB_COUNT];
        let mut carry = 0u64;
        let mut i = 0;
        while i < 5 {
            let sum = a.0[i] + b.0[i] + carry;
            out[i] = sum & LIMB52_MASK;
            carry = sum >> 52;
            i += 1;
        }
        Self(out).sub(&SCALAR_L)
    }

    fn sub(&self, rhs: &Self) -> Self {
        let mut out = [0u64; LIMB_COUNT];
        let mut borrow = 0u64;
        let mut i = 0;
        while i < 5 {
            let diff = self.0[i].wrapping_sub(rhs.0[i] + (borrow >> 63));
            out[i] = diff & LIMB52_MASK;
            borrow = diff;
            i += 1;
        }

        let mut reduced = Self(out);
        if (borrow >> 63) != 0 {
            reduced.add_l();
        }
        reduced
    }

    fn add_l(&mut self) {
        let mut carry = 0u64;
        let mut i = 0;
        while i < 5 {
            let sum = self.0[i] + SCALAR_L.0[i] + carry;
            self.0[i] = sum & LIMB52_MASK;
            carry = sum >> 52;
            i += 1;
        }
    }

    fn montgomery_mul(&self, rhs: &Self) -> Self {
        Self::montgomery_reduce(&Self::mul_internal(self, rhs))
    }

    fn mul_internal(a: &Self, b: &Self) -> [u128; 2 * LIMB_COUNT - 1] {
        let a = &a.0;
        let b = &b.0;

        [
            m(a[0], b[0]),
            m(a[0], b[1]) + m(a[1], b[0]),
            m(a[0], b[2]) + m(a[1], b[1]) + m(a[2], b[0]),
            m(a[0], b[3]) + m(a[1], b[2]) + m(a[2], b[1]) + m(a[3], b[0]),
            m(a[0], b[4]) + m(a[1], b[3]) + m(a[2], b[2]) + m(a[3], b[1]) + m(a[4], b[0]),
            m(a[1], b[4]) + m(a[2], b[3]) + m(a[3], b[2]) + m(a[4], b[1]),
            m(a[2], b[4]) + m(a[3], b[3]) + m(a[4], b[2]),
            m(a[3], b[4]) + m(a[4], b[3]),
            m(a[4], b[4]),
        ]
    }

    fn montgomery_reduce(limbs: &[u128; 2 * LIMB_COUNT - 1]) -> Self {
        // Fold one Montgomery quotient limb into the accumulator.
        #[inline(always)]
        fn part1(sum: u128) -> (u128, u64) {
            let p = (sum as u64).wrapping_mul(SCALAR_LFACTOR) & LIMB52_MASK;
            ((sum + m(p, SCALAR_L.0[0])) >> 52, p)
        }

        // Split a reduced accumulator column into carry and output limb.
        #[inline(always)]
        fn part2(sum: u128) -> (u128, u64) {
            (sum >> 52, (sum as u64) & LIMB52_MASK)
        }

        let l = &SCALAR_L.0;
        let (carry, n0) = part1(limbs[0]);
        let (carry, n1) = part1(carry + limbs[1] + m(n0, l[1]));
        let (carry, n2) = part1(carry + limbs[2] + m(n0, l[2]) + m(n1, l[1]));
        let (carry, n3) = part1(carry + limbs[3] + m(n1, l[2]) + m(n2, l[1]));
        let (carry, n4) = part1(carry + limbs[4] + m(n0, l[4]) + m(n2, l[2]) + m(n3, l[1]));

        let (carry, r0) = part2(carry + limbs[5] + m(n1, l[4]) + m(n3, l[2]) + m(n4, l[1]));
        let (carry, r1) = part2(carry + limbs[6] + m(n2, l[4]) + m(n4, l[2]));
        let (carry, r2) = part2(carry + limbs[7] + m(n3, l[4]));
        let (carry, r3) = part2(carry + limbs[8] + m(n4, l[4]));
        let r4 = carry as u64;

        Self([r0, r1, r2, r3, r4]).sub(&SCALAR_L)
    }

    #[cfg(test)]
    fn from_wide_bytes(bytes: &[u8; 64]) -> Self {
        let words = [
            load_u64(bytes, 0),
            load_u64(bytes, 8),
            load_u64(bytes, 16),
            load_u64(bytes, 24),
            load_u64(bytes, 32),
            load_u64(bytes, 40),
            load_u64(bytes, 48),
            load_u64(bytes, 56),
        ];
        Self::from_wide_words(&words)
    }
}

#[inline(always)]
fn m(lhs: u64, rhs: u64) -> u128 {
    (lhs as u128) * (rhs as u128)
}

#[cfg(test)]
fn load_u64(bytes: &[u8; 64], offset: usize) -> u64 {
    let mut word = [0u8; 8];
    word.copy_from_slice(&bytes[offset..offset + 8]);
    u64::from_le_bytes(word)
}

#[cfg(test)]
fn reduce_wide_slow(bytes: [u8; 64]) -> [u8; 32] {
    use num_bigint::BigUint;
    use std::sync::LazyLock;

    static MODULUS: LazyLock<BigUint> = LazyLock::new(|| BigUint::from_bytes_le(&L_BYTES));

    let reduced = (BigUint::from_bytes_le(&bytes) % &*MODULUS).to_bytes_le();
    let mut out = [0u8; 32];
    out[..reduced.len()].copy_from_slice(&reduced);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{RngCore, SeedableRng, rngs::StdRng};

    /// Reconstruct a scalar from its signed radix-16 digits.
    fn value_from_digits(digits: &Radix16) -> [u8; 32] {
        let mut acc = [0u64; 4];
        let mut i = 64;
        while i > 0 {
            i -= 1;
            // acc *= 16
            let mut carry = 0u64;
            let mut l = 0;
            while l < 4 {
                let next = acc[l] >> 60;
                acc[l] = (acc[l] << 4) | carry;
                carry = next;
                l += 1;
            }
            // acc += sign_extend(digits[i])
            let d = digits[i] as i64;
            let addend = [
                d as u64,
                if d < 0 { u64::MAX } else { 0 },
                if d < 0 { u64::MAX } else { 0 },
                if d < 0 { u64::MAX } else { 0 },
            ];
            let mut carry = 0u128;
            let mut l = 0;
            while l < 4 {
                let sum = acc[l] as u128 + addend[l] as u128 + carry;
                acc[l] = sum as u64;
                carry = sum >> 64;
                l += 1;
            }
        }
        let mut out = [0u8; 32];
        let mut l = 0;
        while l < 4 {
            out[l * 8..l * 8 + 8].copy_from_slice(&acc[l].to_le_bytes());
            l += 1;
        }
        out
    }

    #[test]
    fn radix16_is_carry_loop_equivalent_and_in_range() {
        let mut cases: Vec<[u8; 32]> = Vec::new();
        let mut l_minus_1 = L_BYTES;
        l_minus_1[0] -= 1;
        cases.push([0u8; 32]);
        cases.push({
            let mut b = [0u8; 32];
            b[0] = 1;
            b
        });
        cases.push({
            let mut b = [0u8; 32];
            b[0] = 8;
            b
        });
        cases.push({
            let mut b = [0u8; 32];
            b[0] = 9;
            b
        });
        cases.push(l_minus_1);

        let mut rng = StdRng::seed_from_u64(0x243f_6a88_85a3_08d3);
        for _ in 0..4096 {
            let mut b = [0u8; 32];
            rng.fill_bytes(&mut b);
            b[31] &= 0x0f; // keep it below L
            if is_canonical(&b) {
                cases.push(b);
            }
        }

        for bytes in cases {
            let scalar = Scalar::from_canonical_bytes(bytes);
            let new = scalar.to_radix16();
            let old = scalar.to_radix16_carry_loop();

            // Both must represent exactly the scalar.
            assert_eq!(value_from_digits(&new), bytes, "new digits for {bytes:?}");
            assert_eq!(value_from_digits(&old), bytes, "old digits for {bytes:?}");

            // Check the bounds required by the point tables.
            for (i, &d) in new.iter().enumerate() {
                assert!((-8..=8).contains(&d), "digit {i} = {d}");
                assert!((-8..=8).contains(&-d), "negated digit {i} = {}", -d);
            }
            for pair in 0..32 {
                let folded = new[pair * 2] as i32 + ((new[pair * 2 + 1] as i32) << 4);
                assert!(
                    (-136..=136).contains(&folded),
                    "base pair {pair} = {folded}"
                );
            }
        }
    }

    #[test]
    fn canonical_bound() {
        assert!(!is_canonical(&L_BYTES));
        let mut below = L_BYTES;
        below[0] -= 1;
        assert!(is_canonical(&below));
    }

    #[test]
    fn wide_reduction_matches_slow_reference() {
        let mut cases = [[0u8; 64]; 6];
        cases[1] = [0xff; 64];
        cases[2][0] = 1;
        cases[3][31] = 0x80;
        cases[4][32] = 1;
        cases[5][63] = 0x80;

        for bytes in cases {
            let reduced = reduce_wide(bytes);
            assert_eq!(reduced, reduce_wide_slow(bytes));
            assert!(is_canonical(&reduced));
        }

        let mut rng = StdRng::seed_from_u64(0x6a09_e667_f3bc_c908);
        let mut round = 0;
        while round < 2048 {
            let mut bytes = [0u8; 64];
            rng.fill_bytes(&mut bytes);

            let reduced = reduce_wide(bytes);
            assert_eq!(reduced, reduce_wide_slow(bytes), "round {round}");
            assert!(is_canonical(&reduced), "round {round}");
            round += 1;
        }
    }
}
