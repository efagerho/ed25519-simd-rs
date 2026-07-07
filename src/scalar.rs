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
        // Scalars are always reduced mod L < 2^253, so the final carry out of
        // digit 63 (which would need a 65th digit) is provably always zero.
        debug_assert_eq!(carry, 0, "radix-16 carry out of a scalar reduced mod L");
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
        #[inline(always)]
        fn part1(sum: u128) -> (u128, u64) {
            let p = (sum as u64).wrapping_mul(SCALAR_LFACTOR) & LIMB52_MASK;
            ((sum + m(p, SCALAR_L.0[0])) >> 52, p)
        }

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
    let modulus = u256_from_le_bytes(&L_BYTES);
    let mut r = [0u64; 4];

    let mut bit = 512;
    while bit > 0 {
        bit -= 1;
        shl1(&mut r);
        if get_bit(&bytes, bit) {
            r[0] |= 1;
        }
        if cmp_u256(&r, &modulus) != core::cmp::Ordering::Less {
            sub_u256(&mut r, &modulus);
        }
    }

    u256_to_le_bytes(r)
}

#[cfg(test)]
fn get_bit(bytes: &[u8], bit: usize) -> bool {
    ((bytes[bit / 8] >> (bit % 8)) & 1) != 0
}

#[cfg(test)]
fn u256_from_le_bytes(bytes: &[u8; 32]) -> [u64; 4] {
    let mut out = [0u64; 4];
    let mut i = 0;
    while i < 4 {
        let mut limb = [0u8; 8];
        limb.copy_from_slice(&bytes[i * 8..i * 8 + 8]);
        out[i] = u64::from_le_bytes(limb);
        i += 1;
    }
    out
}

#[cfg(test)]
fn u256_to_le_bytes(limbs: [u64; 4]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut i = 0;
    while i < 4 {
        out[i * 8..i * 8 + 8].copy_from_slice(&limbs[i].to_le_bytes());
        i += 1;
    }
    out
}

#[cfg(test)]
fn shl1(value: &mut [u64; 4]) {
    let mut carry = 0u64;
    let mut i = 0;
    while i < 4 {
        let next = value[i] >> 63;
        value[i] = (value[i] << 1) | carry;
        carry = next;
        i += 1;
    }
}

#[cfg(test)]
fn cmp_u256(a: &[u64; 4], b: &[u64; 4]) -> core::cmp::Ordering {
    let mut i = 4;
    while i > 0 {
        i -= 1;
        match a[i].cmp(&b[i]) {
            core::cmp::Ordering::Equal => {}
            ord => return ord,
        }
    }
    core::cmp::Ordering::Equal
}

#[cfg(test)]
fn sub_u256(a: &mut [u64; 4], b: &[u64; 4]) {
    let mut borrow = 0u128;
    let base = 1u128 << 64;
    let mut i = 0;
    while i < 4 {
        let ai = a[i] as u128;
        let bi = b[i] as u128 + borrow;
        if ai >= bi {
            a[i] = (ai - bi) as u64;
            borrow = 0;
        } else {
            a[i] = (ai + base - bi) as u64;
            borrow = 1;
        }
        i += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

        let mut state = 0x6a09e667f3bcc908u64;
        let mut round = 0;
        while round < 2048 {
            let mut bytes = [0u8; 64];
            let mut i = 0;
            while i < 8 {
                state = state
                    .wrapping_mul(0xd1342543de82ef95)
                    .wrapping_add(0x9e3779b97f4a7c15);
                bytes[i * 8..i * 8 + 8].copy_from_slice(&state.to_le_bytes());
                i += 1;
            }

            let reduced = reduce_wide(bytes);
            assert_eq!(reduced, reduce_wide_slow(bytes), "round {round}");
            assert!(is_canonical(&reduced), "round {round}");
            round += 1;
        }
    }
}
