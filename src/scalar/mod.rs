const L_BYTES: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
];

pub(crate) type Radix16 = [i8; 64];
const LANES: usize = crate::batch::SIMD_LANES;
const WIDE_WORDS: usize = 8;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Scalar {
    bytes: [u8; 32],
}

impl Scalar {
    pub(crate) fn from_canonical_bytes(bytes: [u8; 32]) -> Self {
        debug_assert!(is_canonical(&bytes));
        Self { bytes }
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
}

/// Reduce eight 512-bit challenge hashes modulo the group order and recode
/// them as signed radix-16 digits. Each input row is one word across all lanes.
pub(crate) fn wide_words_to_radix16(words: &[[u64; LANES]; WIDE_WORDS]) -> [Radix16; LANES] {
    wide::wide_words_to_radix16(words)
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

mod wide;

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
    fn radix16_represents_scalar_and_stays_in_range() {
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
            let digits = scalar.to_radix16();

            assert_eq!(value_from_digits(&digits), bytes, "digits for {bytes:?}");

            // Check the bounds required by the point tables.
            for (i, &d) in digits.iter().enumerate() {
                assert!((-8..=8).contains(&d), "digit {i} = {d}");
                assert!((-8..=8).contains(&-d), "negated digit {i} = {}", -d);
            }
            for pair in 0..32 {
                let folded = digits[pair * 2] as i32 + ((digits[pair * 2 + 1] as i32) << 4);
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
}
