use super::{LANES, Radix16, WIDE_WORDS};

/// Reduce eight 512-bit challenge hashes modulo the group order and recode
/// them as signed radix-16 digits. Each input row is one word across all lanes.
pub(super) fn wide_words_to_radix16(words: &[[u64; LANES]; WIDE_WORDS]) -> [Radix16; LANES] {
    WideScalar52::from_wide_words(words).to_radix16()
}

const LIMB52_MASK: u64 = (1u64 << 52) - 1;
// Number of 52-bit limbs needed to represent a value modulo L, the group order.
const LIMB_COUNT: usize = 5;
const SCALAR_L: [u64; LIMB_COUNT] = [
    0x0002631a5cf5d3ed,
    0x000dea2f79cd6581,
    0x000000000014def9,
    0x0000000000000000,
    0x0000100000000000,
];
const SCALAR_LFACTOR: u64 = 0x51da312547e1b;
const SCALAR_R: [u64; LIMB_COUNT] = [
    0x000f48bd6721e6ed,
    0x0003bab5ac67e45a,
    0x000fffffeb35e51b,
    0x000fffffffffffff,
    0x00000fffffffffff,
];
const SCALAR_RR: [u64; LIMB_COUNT] = [
    0x0009d265e952d13b,
    0x000d63c715bea69f,
    0x0005be65cb687604,
    0x0003dceec73d217f,
    0x000009411b7c309a,
];

#[derive(Clone, Copy)]
struct WideScalar52([std::arch::x86_64::__m512i; LIMB_COUNT]);

impl WideScalar52 {
    fn from_wide_words(words: &[[u64; LANES]; WIDE_WORDS]) -> Self {
        use std::arch::x86_64::*;
        unsafe {
            let mask = _mm512_set1_epi64(LIMB52_MASK as i64);
            let words: [__m512i; WIDE_WORDS] = core::array::from_fn(|i| loadu(words[i]));
            let lo = Self([
                _mm512_and_si512(words[0], mask),
                _mm512_and_si512(
                    _mm512_or_si512(
                        _mm512_srli_epi64(words[0], 52),
                        _mm512_slli_epi64(words[1], 12),
                    ),
                    mask,
                ),
                _mm512_and_si512(
                    _mm512_or_si512(
                        _mm512_srli_epi64(words[1], 40),
                        _mm512_slli_epi64(words[2], 24),
                    ),
                    mask,
                ),
                _mm512_and_si512(
                    _mm512_or_si512(
                        _mm512_srli_epi64(words[2], 28),
                        _mm512_slli_epi64(words[3], 36),
                    ),
                    mask,
                ),
                _mm512_and_si512(
                    _mm512_or_si512(
                        _mm512_srli_epi64(words[3], 16),
                        _mm512_slli_epi64(words[4], 48),
                    ),
                    mask,
                ),
            ]);
            let hi = Self([
                _mm512_and_si512(_mm512_srli_epi64(words[4], 4), mask),
                _mm512_and_si512(
                    _mm512_or_si512(
                        _mm512_srli_epi64(words[4], 56),
                        _mm512_slli_epi64(words[5], 8),
                    ),
                    mask,
                ),
                _mm512_and_si512(
                    _mm512_or_si512(
                        _mm512_srli_epi64(words[5], 44),
                        _mm512_slli_epi64(words[6], 20),
                    ),
                    mask,
                ),
                _mm512_and_si512(
                    _mm512_or_si512(
                        _mm512_srli_epi64(words[6], 32),
                        _mm512_slli_epi64(words[7], 32),
                    ),
                    mask,
                ),
                _mm512_srli_epi64(words[7], 20),
            ]);

            Self::add(
                &hi.montgomery_mul(&Self::constant(&SCALAR_RR)),
                &lo.montgomery_mul(&Self::constant(&SCALAR_R)),
            )
        }
    }

    fn constant(value: &[u64; LIMB_COUNT]) -> Self {
        use std::arch::x86_64::*;
        unsafe { Self(core::array::from_fn(|i| _mm512_set1_epi64(value[i] as i64))) }
    }

    fn add(a: &Self, b: &Self) -> Self {
        use std::arch::x86_64::*;
        unsafe {
            let mask = _mm512_set1_epi64(LIMB52_MASK as i64);
            let mut out = [_mm512_setzero_si512(); LIMB_COUNT];
            let mut carry = _mm512_setzero_si512();
            let mut i = 0;
            while i < LIMB_COUNT {
                let sum = _mm512_add_epi64(_mm512_add_epi64(a.0[i], b.0[i]), carry);
                out[i] = _mm512_and_si512(sum, mask);
                carry = _mm512_srli_epi64(sum, 52);
                i += 1;
            }
            Self(out).sub(&Self::constant(&SCALAR_L))
        }
    }

    fn sub(&self, rhs: &Self) -> Self {
        use std::arch::x86_64::*;
        unsafe {
            let limb_mask = _mm512_set1_epi64(LIMB52_MASK as i64);
            let one = _mm512_set1_epi64(1);
            let mut out = [_mm512_setzero_si512(); LIMB_COUNT];
            let mut borrow_mask = 0;
            let mut i = 0;
            while i < LIMB_COUNT {
                let borrow = _mm512_maskz_mov_epi64(borrow_mask, one);
                let subtrahend = _mm512_add_epi64(rhs.0[i], borrow);
                borrow_mask = _mm512_cmplt_epu64_mask(self.0[i], subtrahend);
                out[i] = _mm512_and_si512(_mm512_sub_epi64(self.0[i], subtrahend), limb_mask);
                i += 1;
            }

            let added_l = Self(out).add_l();
            Self(core::array::from_fn(|i| {
                _mm512_mask_blend_epi64(borrow_mask, out[i], added_l.0[i])
            }))
        }
    }

    fn add_l(&self) -> Self {
        use std::arch::x86_64::*;
        unsafe {
            let l = Self::constant(&SCALAR_L);
            let mask = _mm512_set1_epi64(LIMB52_MASK as i64);
            let mut out = [_mm512_setzero_si512(); LIMB_COUNT];
            let mut carry = _mm512_setzero_si512();
            let mut i = 0;
            while i < LIMB_COUNT {
                let sum = _mm512_add_epi64(_mm512_add_epi64(self.0[i], l.0[i]), carry);
                out[i] = _mm512_and_si512(sum, mask);
                carry = _mm512_srli_epi64(sum, 52);
                i += 1;
            }
            Self(out)
        }
    }

    fn montgomery_mul(&self, rhs: &Self) -> Self {
        let (lo, hi) = Self::mul_internal(self, rhs);
        Self::montgomery_reduce(&lo, &hi)
    }

    fn mul_internal(
        a: &Self,
        b: &Self,
    ) -> (
        [std::arch::x86_64::__m512i; 2 * LIMB_COUNT - 1],
        [std::arch::x86_64::__m512i; 2 * LIMB_COUNT - 1],
    ) {
        use std::arch::x86_64::*;
        unsafe {
            let mut lo = [_mm512_setzero_si512(); 2 * LIMB_COUNT - 1];
            let mut hi = [_mm512_setzero_si512(); 2 * LIMB_COUNT - 1];
            let mut i = 0;
            while i < LIMB_COUNT {
                let mut j = 0;
                while j < LIMB_COUNT {
                    lo[i + j] = _mm512_madd52lo_epu64(lo[i + j], a.0[i], b.0[j]);
                    hi[i + j] = _mm512_madd52hi_epu64(hi[i + j], a.0[i], b.0[j]);
                    j += 1;
                }
                i += 1;
            }
            (lo, hi)
        }
    }

    fn montgomery_reduce(
        lo: &[std::arch::x86_64::__m512i; 2 * LIMB_COUNT - 1],
        hi: &[std::arch::x86_64::__m512i; 2 * LIMB_COUNT - 1],
    ) -> Self {
        use std::arch::x86_64::*;

        #[inline(always)]
        fn add_product(lo: &mut __m512i, hi: &mut __m512i, lhs: __m512i, rhs: __m512i) {
            unsafe {
                *lo = _mm512_madd52lo_epu64(*lo, lhs, rhs);
                *hi = _mm512_madd52hi_epu64(*hi, lhs, rhs);
            }
        }

        #[inline(always)]
        fn eliminate_low_limb(
            mut lo: __m512i,
            mut hi: __m512i,
            carry: __m512i,
            factor: __m512i,
            l0: __m512i,
        ) -> (__m512i, __m512i) {
            unsafe {
                lo = _mm512_add_epi64(lo, carry);
                let quotient = _mm512_madd52lo_epu64(_mm512_setzero_si512(), lo, factor);
                add_product(&mut lo, &mut hi, quotient, l0);
                let carry = _mm512_add_epi64(hi, _mm512_srli_epi64(lo, 52));
                (quotient, carry)
            }
        }

        #[inline(always)]
        fn split_output_limb(
            lo: __m512i,
            hi: __m512i,
            carry: __m512i,
            mask: __m512i,
        ) -> (__m512i, __m512i) {
            unsafe {
                let lo = _mm512_add_epi64(lo, carry);
                (
                    _mm512_add_epi64(hi, _mm512_srli_epi64(lo, 52)),
                    _mm512_and_si512(lo, mask),
                )
            }
        }

        unsafe {
            let zero = _mm512_setzero_si512();
            let mask = _mm512_set1_epi64(LIMB52_MASK as i64);
            let factor = _mm512_set1_epi64(SCALAR_LFACTOR as i64);
            let l = Self::constant(&SCALAR_L).0;

            let (n0, carry) = eliminate_low_limb(lo[0], hi[0], zero, factor, l[0]);

            let (mut s_lo, mut s_hi) = (lo[1], hi[1]);
            add_product(&mut s_lo, &mut s_hi, n0, l[1]);
            let (n1, carry) = eliminate_low_limb(s_lo, s_hi, carry, factor, l[0]);

            let (mut s_lo, mut s_hi) = (lo[2], hi[2]);
            add_product(&mut s_lo, &mut s_hi, n0, l[2]);
            add_product(&mut s_lo, &mut s_hi, n1, l[1]);
            let (n2, carry) = eliminate_low_limb(s_lo, s_hi, carry, factor, l[0]);

            let (mut s_lo, mut s_hi) = (lo[3], hi[3]);
            add_product(&mut s_lo, &mut s_hi, n1, l[2]);
            add_product(&mut s_lo, &mut s_hi, n2, l[1]);
            let (n3, carry) = eliminate_low_limb(s_lo, s_hi, carry, factor, l[0]);

            let (mut s_lo, mut s_hi) = (lo[4], hi[4]);
            add_product(&mut s_lo, &mut s_hi, n0, l[4]);
            add_product(&mut s_lo, &mut s_hi, n2, l[2]);
            add_product(&mut s_lo, &mut s_hi, n3, l[1]);
            let (n4, carry) = eliminate_low_limb(s_lo, s_hi, carry, factor, l[0]);

            let (mut s_lo, mut s_hi) = (lo[5], hi[5]);
            add_product(&mut s_lo, &mut s_hi, n1, l[4]);
            add_product(&mut s_lo, &mut s_hi, n3, l[2]);
            add_product(&mut s_lo, &mut s_hi, n4, l[1]);
            let (carry, r0) = split_output_limb(s_lo, s_hi, carry, mask);

            let (mut s_lo, mut s_hi) = (lo[6], hi[6]);
            add_product(&mut s_lo, &mut s_hi, n2, l[4]);
            add_product(&mut s_lo, &mut s_hi, n4, l[2]);
            let (carry, r1) = split_output_limb(s_lo, s_hi, carry, mask);

            let (mut s_lo, mut s_hi) = (lo[7], hi[7]);
            add_product(&mut s_lo, &mut s_hi, n3, l[4]);
            let (carry, r2) = split_output_limb(s_lo, s_hi, carry, mask);

            let (mut s_lo, mut s_hi) = (lo[8], hi[8]);
            add_product(&mut s_lo, &mut s_hi, n4, l[4]);
            let (r4, r3) = split_output_limb(s_lo, s_hi, carry, mask);

            Self([r0, r1, r2, r3, r4]).sub(&Self::constant(&SCALAR_L))
        }
    }

    fn words(self) -> [std::arch::x86_64::__m512i; 4] {
        use std::arch::x86_64::*;
        unsafe {
            [
                _mm512_or_si512(self.0[0], _mm512_slli_epi64(self.0[1], 52)),
                _mm512_or_si512(
                    _mm512_srli_epi64(self.0[1], 12),
                    _mm512_slli_epi64(self.0[2], 40),
                ),
                _mm512_or_si512(
                    _mm512_srli_epi64(self.0[2], 24),
                    _mm512_slli_epi64(self.0[3], 28),
                ),
                _mm512_or_si512(
                    _mm512_srli_epi64(self.0[3], 36),
                    _mm512_slli_epi64(self.0[4], 16),
                ),
            ]
        }
    }

    #[cfg(test)]
    fn to_bytes_lanes(self) -> [[u8; 32]; LANES] {
        let words = self.words();
        let mut rows = [[0u64; LANES]; 4];
        for (word, row) in rows.iter_mut().enumerate() {
            storeu(words[word], row);
        }
        core::array::from_fn(|lane| {
            let mut bytes = [0u8; 32];
            for word in 0..4 {
                bytes[word * 8..word * 8 + 8].copy_from_slice(&rows[word][lane].to_le_bytes());
            }
            bytes
        })
    }

    fn to_radix16(self) -> [Radix16; LANES] {
        use std::arch::x86_64::*;
        unsafe {
            let words = self.words();
            let byte_mask = _mm512_set1_epi64(0xff);
            let nibble_mask = _mm512_set1_epi64(0x0f);
            let bias = _mm512_set1_epi64(0x88);
            let eight = _mm512_set1_epi64(8);
            let mut carry = _mm512_setzero_si512();
            let mut out = [[0i8; 64]; LANES];
            let mut lanes = [0u64; LANES];

            let mut byte = 0;
            while byte < 32 {
                let shifts = _mm512_set1_epi64(((byte & 7) * 8) as i64);
                let value = _mm512_and_si512(_mm512_srlv_epi64(words[byte / 8], shifts), byte_mask);
                let biased = _mm512_add_epi64(_mm512_add_epi64(value, bias), carry);
                carry = _mm512_srli_epi64(biased, 8);

                let low = _mm512_sub_epi64(_mm512_and_si512(biased, nibble_mask), eight);
                let high = _mm512_sub_epi64(
                    _mm512_and_si512(_mm512_srli_epi64(biased, 4), nibble_mask),
                    eight,
                );
                storeu(low, &mut lanes);
                for lane in 0..LANES {
                    out[lane][2 * byte] = lanes[lane] as i8;
                }
                storeu(high, &mut lanes);
                for lane in 0..LANES {
                    out[lane][2 * byte + 1] = lanes[lane] as i8;
                }
                byte += 1;
            }

            storeu(carry, &mut lanes);
            debug_assert_eq!(lanes, [0; LANES]);
            out
        }
    }
}

#[inline(always)]
fn loadu(values: [u64; LANES]) -> std::arch::x86_64::__m512i {
    unsafe { std::arch::x86_64::_mm512_loadu_si512(values.as_ptr() as *const _) }
}

#[inline(always)]
fn storeu(value: std::arch::x86_64::__m512i, out: &mut [u64; LANES]) {
    unsafe { std::arch::x86_64::_mm512_storeu_si512(out.as_mut_ptr() as *mut _, value) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::is_canonical;

    #[test]
    fn eight_lane_reduction_and_radix16_match_vectors() {
        let fixture: serde_json::Value =
            serde_json::from_str(include_str!("../../tests/vectors/scalar_reduction.json"))
                .unwrap();
        let cases = fixture["cases"].as_array().unwrap();
        assert_eq!(cases.len(), LANES);

        let words: [[u64; LANES]; WIDE_WORDS] = core::array::from_fn(|word| {
            core::array::from_fn(|lane| cases[lane]["words"][word].as_u64().unwrap())
        });
        let wide = WideScalar52::from_wide_words(&words);
        let reduced = wide.to_bytes_lanes();
        let digits = wide_words_to_radix16(&words);

        for lane in 0..LANES {
            let mut expected_reduced = [0u8; 32];
            hex::decode_to_slice(
                cases[lane]["reduced"].as_str().unwrap(),
                &mut expected_reduced,
            )
            .unwrap();
            let expected_digits: Radix16 =
                core::array::from_fn(|digit| cases[lane]["radix16"][digit].as_i64().unwrap() as i8);

            assert_eq!(reduced[lane], expected_reduced, "lane {lane} reduction");
            assert_eq!(digits[lane], expected_digits, "lane {lane} recoding");
            assert!(is_canonical(&reduced[lane]), "lane {lane} canonicality");
        }
    }
}
