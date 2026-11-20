use super::{LANES, Radix16, WIDE_WORDS};

/// Reduce eight 512-bit challenge hashes modulo the group order and recode
/// them as signed radix-16 digits. Each input row is one word across all lanes.
pub(super) fn wide_words_to_radix16(words: &[[u64; LANES]; WIDE_WORDS]) -> [Radix16; LANES] {
    WideScalar52::from_wide_words_rust(words).to_radix16()
}

// Five radix-2^52 limbs cover the scalar modulus.
const LIMB_COUNT: usize = 5;

mod rust;

/// Eight scalars packed limbwise for parallel AVX-512 modular arithmetic.
///
/// Each vector holds one 52-bit limb from eight SHA-512 hashes,
/// so one IFMA Montgomery multiplication advances all eight reductions.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct WideScalar52([std::arch::x86_64::__m512i; LIMB_COUNT]);

const _: () = {
    assert!(core::mem::size_of::<WideScalar52>() == 320);
    assert!(core::mem::align_of::<WideScalar52>() == 64);
};

impl WideScalar52 {
    #[cfg(test)]
    /// Reduces all 512 input bits to canonical radix-2^52 residues modulo L.
    fn from_wide_words(words: &[[u64; LANES]; WIDE_WORDS]) -> Self {
        #[cfg(all(
            feature = "asm",
            target_os = "linux",
            target_arch = "x86_64",
            target_pointer_width = "64"
        ))]
        {
            let mut out = core::mem::MaybeUninit::<Self>::uninit();
            // The buffers are disjoint, and the assembly initializes all five
            // output vectors. Input words may be only eight-byte aligned.
            unsafe {
                super::asm::ed25519_simd_scalar_reduce_ifma(
                    out.as_mut_ptr().cast(),
                    words.as_ptr().cast(),
                );
                out.assume_init()
            }
        }
        #[cfg(not(all(
            feature = "asm",
            target_os = "linux",
            target_arch = "x86_64",
            target_pointer_width = "64"
        )))]
        Self::from_wide_words_rust(words)
    }

    /// Packs each lane's five radix-2^52 limbs into four little-endian 64-bit
    /// words.
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

    /// Serializes each lane as a 32-byte little-endian scalar.
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

    /// Recodes each lane as 64 little-endian signed radix-16 digits in
    /// `-8..=7`.
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

// Loads the eight `u64` lanes into a 512-bit SIMD vector without requiring alignment.
#[inline(always)]
fn loadu(values: [u64; LANES]) -> std::arch::x86_64::__m512i {
    unsafe { std::arch::x86_64::_mm512_loadu_si512(values.as_ptr() as *const _) }
}

// Stores a 512-bit SIMD vector into eight `u64` lanes without requiring alignment.
#[inline(always)]
fn storeu(value: std::arch::x86_64::__m512i, out: &mut [u64; LANES]) {
    unsafe { std::arch::x86_64::_mm512_storeu_si512(out.as_mut_ptr() as *mut _, value) }
}

#[cfg(test)]
mod tests;
