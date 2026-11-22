use crate::batch::{R_ENCODING_LEN, SIMD_LANES, challenge_block_count};
use crate::input::PUBLIC_KEY_LEN;

const IV: [u64; 8] = [
    0x6a09e667f3bcc908,
    0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1,
    0x510e527fade682d1,
    0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179,
];

const K: [u64; 80] = [
    0x428a2f98d728ae22,
    0x7137449123ef65cd,
    0xb5c0fbcfec4d3b2f,
    0xe9b5dba58189dbbc,
    0x3956c25bf348b538,
    0x59f111f1b605d019,
    0x923f82a4af194f9b,
    0xab1c5ed5da6d8118,
    0xd807aa98a3030242,
    0x12835b0145706fbe,
    0x243185be4ee4b28c,
    0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f,
    0x80deb1fe3b1696b1,
    0x9bdc06a725c71235,
    0xc19bf174cf692694,
    0xe49b69c19ef14ad2,
    0xefbe4786384f25e3,
    0x0fc19dc68b8cd5b5,
    0x240ca1cc77ac9c65,
    0x2de92c6f592b0275,
    0x4a7484aa6ea6e483,
    0x5cb0a9dcbd41fbd4,
    0x76f988da831153b5,
    0x983e5152ee66dfab,
    0xa831c66d2db43210,
    0xb00327c898fb213f,
    0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2,
    0xd5a79147930aa725,
    0x06ca6351e003826f,
    0x142929670a0e6e70,
    0x27b70a8546d22ffc,
    0x2e1b21385c26c926,
    0x4d2c6dfc5ac42aed,
    0x53380d139d95b3df,
    0x650a73548baf63de,
    0x766a0abb3c77b2a8,
    0x81c2c92e47edaee6,
    0x92722c851482353b,
    0xa2bfe8a14cf10364,
    0xa81a664bbc423001,
    0xc24b8b70d0f89791,
    0xc76c51a30654be30,
    0xd192e819d6ef5218,
    0xd69906245565a910,
    0xf40e35855771202a,
    0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8,
    0x1e376c085141ab53,
    0x2748774cdf8eeb99,
    0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63,
    0x4ed8aa4ae3418acb,
    0x5b9cca4f7763e373,
    0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc,
    0x78a5636f43172f60,
    0x84c87814a1f0ab72,
    0x8cc702081a6439ec,
    0x90befffa23631e28,
    0xa4506cebde82bde9,
    0xbef9a3f7b2c67915,
    0xc67178f2e372532b,
    0xca273eceea26619c,
    0xd186b8c721c0c207,
    0xeada7dd6cde0eb1e,
    0xf57d4f7fee6ed178,
    0x06f067aa72176fba,
    0x0a637dc5a2c898a6,
    0x113f9804bef90dae,
    0x1b710b35131c471b,
    0x28db77f523047d84,
    0x32caab7b40c72493,
    0x3c9ebe0a15c9bebc,
    0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6,
    0x597f299cfc657e2a,
    0x5fcb6fab3ad6faec,
    0x6c44198c4a475817,
];

/// Independent `sha2`-backed reference for the AVX-512 path.
#[cfg(test)]
pub(crate) fn hash_slices(slices: &[&[u8]]) -> [u8; 64] {
    use sha2::Digest;
    let mut hasher = sha2::Sha512::new();
    for slice in slices {
        hasher.update(slice);
    }
    hasher.finalize().into()
}

/// Test reference returning challenge hashes as bytes.
#[cfg(test)]
pub(crate) fn hash_ed25519_challenges(
    r_bytes: &[[u8; R_ENCODING_LEN]; SIMD_LANES],
    public_keys: &[[u8; PUBLIC_KEY_LEN]; SIMD_LANES],
    messages: [&[u8]; SIMD_LANES],
) -> [[u8; 64]; SIMD_LANES] {
    let words = hash_ed25519_challenge_words(r_bytes, public_keys, messages);
    core::array::from_fn(|lane| {
        let mut digest = [0u8; 64];
        for word in 0..8 {
            digest[word * 8..word * 8 + 8].copy_from_slice(&words[word][lane].to_le_bytes());
        }
        digest
    })
}

/// Challenge hashes in the word-major layout consumed by the wide scalar reducer.
pub(crate) use avx512::hash_ed25519_challenge_words;

mod avx512 {

    use super::{IV, K, PUBLIC_KEY_LEN, R_ENCODING_LEN, SIMD_LANES, challenge_block_count};
    use std::arch::x86_64::*;

    const LANES: usize = SIMD_LANES;

    /// Hash eight challenges, freezing each lane after its length trailer.
    #[inline(never)]
    pub(crate) fn hash_ed25519_challenge_words(
        r_bytes: &[[u8; R_ENCODING_LEN]; LANES],
        public_keys: &[[u8; PUBLIC_KEY_LEN]; LANES],
        messages: [&[u8]; LANES],
    ) -> [[u64; LANES]; 8] {
        unsafe {
            let total_lens = messages.map(|m| (64 + m.len()) as u64);
            let counts = messages.map(|m| challenge_block_count(m.len()) as u64);
            let last = loadu(counts.map(|count| count - 1));
            let (length_hi, length_lo) = bit_lengths(total_lens);

            let mut state = [
                _mm512_set1_epi64(IV[0] as i64),
                _mm512_set1_epi64(IV[1] as i64),
                _mm512_set1_epi64(IV[2] as i64),
                _mm512_set1_epi64(IV[3] as i64),
                _mm512_set1_epi64(IV[4] as i64),
                _mm512_set1_epi64(IV[5] as i64),
                _mm512_set1_epi64(IV[6] as i64),
                _mm512_set1_epi64(IV[7] as i64),
            ];

            for block in 0..*counts.iter().max().unwrap() as usize {
                let index = _mm512_set1_epi64(block as i64);
                let first = if block == 0 {
                    encoded_prefix_words(r_bytes, public_keys)
                } else {
                    message_words(&messages, 128 * block - 64)
                };
                let second = message_words(&messages, 128 * block);
                let mut words: [__m512i; 16] = [first, second].as_flattened().try_into().unwrap();
                let ending = _mm512_cmpeq_epu64_mask(last, index);
                words[14] = _mm512_mask_mov_epi64(words[14], ending, length_hi);
                words[15] = _mm512_mask_mov_epi64(words[15], ending, length_lo);

                let active = _mm512_cmpge_epu64_mask(last, index);
                let previous = state;
                compress_block(&mut state, words);
                if active != 0xff {
                    for word in 0..8 {
                        state[word] = _mm512_mask_blend_epi64(active, previous[word], state[word]);
                    }
                }
            }

            digest_words_from_state(state)
        }
    }

    fn bit_lengths(total_lens: [u64; LANES]) -> (__m512i, __m512i) {
        let lengths = loadu(total_lens);
        unsafe {
            (
                _mm512_srli_epi64::<61>(lengths),
                _mm512_slli_epi64::<3>(lengths),
            )
        }
    }

    /// Load one half-block per lane. Only the half containing the end of the
    /// message receives the padding bit, including at an exact 64-byte boundary.
    fn message_words(messages: &[&[u8]; LANES], offset: usize) -> [__m512i; 8] {
        let rows = messages.map(|message| unsafe {
            match message.get(offset..) {
                Some(tail) if tail.len() >= 64 => _mm512_loadu_si512(tail.as_ptr().cast()),
                Some(tail) => {
                    let pad = 1u64 << tail.len();
                    // Masked-off bytes are never read, including for an empty slice.
                    let data = _mm512_maskz_loadu_epi8(pad - 1, tail.as_ptr().cast());
                    _mm512_mask_set1_epi8(data, pad, -128)
                }
                None => _mm512_setzero_si512(),
            }
        });
        transpose_message_words(rows)
    }

    /// Unpack adjacent rows, then join pairs and quartets into eight columns.
    fn transpose_message_words(rows: [__m512i; 8]) -> [__m512i; 8] {
        unsafe {
            let even =
                core::array::from_fn(|i| _mm512_unpacklo_epi64(rows[2 * i], rows[2 * i + 1]));
            let odd = core::array::from_fn(|i| _mm512_unpackhi_epi64(rows[2 * i], rows[2 * i + 1]));
            let [w0, w4] = columns::<0x88>(even);
            let [w2, w6] = columns::<0xdd>(even);
            let [w1, w5] = columns::<0x88>(odd);
            let [w3, w7] = columns::<0xdd>(odd);
            [w0, w1, w2, w3, w4, w5, w6, w7].map(byte_swap_lanes)
        }
    }

    #[inline(always)]
    fn columns<const SELECT: i32>([a, b, c, d]: [__m512i; 4]) -> [__m512i; 2] {
        unsafe {
            let low = _mm512_shuffle_i64x2::<SELECT>(a, b);
            let high = _mm512_shuffle_i64x2::<SELECT>(c, d);
            [
                _mm512_shuffle_i64x2::<0x88>(low, high),
                _mm512_shuffle_i64x2::<0xdd>(low, high),
            ]
        }
    }

    fn encoded_prefix_words(
        r_bytes: &[[u8; R_ENCODING_LEN]; LANES],
        public_keys: &[[u8; PUBLIC_KEY_LEN]; LANES],
    ) -> [__m512i; 8] {
        let r = transpose_8x4_be_u64(r_bytes);
        let public_key = transpose_8x4_be_u64(public_keys);
        [
            r[0],
            r[1],
            r[2],
            r[3],
            public_key[0],
            public_key[1],
            public_key[2],
            public_key[3],
        ]
    }

    /// Transpose eight contiguous four-word encodings into the word-major
    /// vectors consumed by SHA-512, swapping each word to big endian on the way.
    fn transpose_8x4_be_u64(rows: &[[u8; 32]; LANES]) -> [__m512i; 4] {
        unsafe {
            let input = rows.as_ptr().cast::<__m512i>();
            let row01 = _mm512_loadu_si512(input);
            let row23 = _mm512_loadu_si512(input.add(1));
            let row45 = _mm512_loadu_si512(input.add(2));
            let row67 = _mm512_loadu_si512(input.add(3));

            core::array::from_fn(|column| {
                let column = column as i64;
                let indices = _mm512_set_epi64(
                    12 + column,
                    8 + column,
                    4 + column,
                    column,
                    12 + column,
                    8 + column,
                    4 + column,
                    column,
                );
                let low = _mm512_permutex2var_epi64(row01, indices, row23);
                let high = _mm512_permutex2var_epi64(row45, indices, row67);
                byte_swap_lanes(_mm512_mask_blend_epi64(0xf0, low, high))
            })
        }
    }

    #[inline(always)]
    fn byte_swap_lanes(value: __m512i) -> __m512i {
        unsafe {
            let shuffle = _mm512_set_epi64(
                0x38393a3b3c3d3e3f,
                0x3031323334353637,
                0x28292a2b2c2d2e2f,
                0x2021222324252627,
                0x18191a1b1c1d1e1f,
                0x1011121314151617,
                0x08090a0b0c0d0e0f,
                0x0001020304050607,
            );
            _mm512_shuffle_epi8(value, shuffle)
        }
    }

    fn compress_block(state: &mut [__m512i; 8], block_words: [__m512i; 16]) {
        let mut w = block_words;
        let mut working = *state;

        // One full turn of the ring gives the compiler constant register
        // indices for all four schedule operands and the eight working words.
        macro_rules! rounds {
            ($($i:literal),*) => {{
                $(working = round(working, w[$i], K[$i]);)*
                for base in (16..80).step_by(16) {
                    $(
                        w[$i] = add4(
                            small_sigma1(w[($i + 14) % 16]),
                            w[($i + 9) % 16],
                            small_sigma0(w[($i + 1) % 16]),
                            w[$i],
                        );
                        working = round(working, w[$i], K[base + $i]);
                    )*
                }
            }};
        }
        rounds!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
        for (word, result) in state.iter_mut().zip(working) {
            *word = add(*word, result);
        }
    }

    #[inline(always)]
    fn round([a, b, c, d, e, f, g, h]: [__m512i; 8], word: __m512i, constant: u64) -> [__m512i; 8] {
        let kw = add(word, unsafe { _mm512_set1_epi64(constant as i64) });
        let t1 = add(add(h, kw), add(big_sigma1(e), ch(e, f, g)));
        let t2 = add(big_sigma0(a), maj(a, b, c));
        [add(t1, t2), a, b, c, add(d, t1), e, f, g]
    }

    /// Digest words pre-swapped to the little-endian integer reduced by RFC 8032.
    fn digest_words_from_state(state: [__m512i; 8]) -> [[u64; LANES]; 8] {
        let mut words = [[0u64; LANES]; 8];
        for (word, &s) in state.iter().enumerate() {
            storeu(byte_swap_lanes(s), &mut words[word]);
        }
        words
    }

    #[inline]
    fn add(a: __m512i, b: __m512i) -> __m512i {
        unsafe { _mm512_add_epi64(a, b) }
    }

    #[inline]
    fn add4(a: __m512i, b: __m512i, c: __m512i, d: __m512i) -> __m512i {
        add(add(a, b), add(c, d))
    }

    #[inline]
    fn ch(x: __m512i, y: __m512i, z: __m512i) -> __m512i {
        unsafe { _mm512_xor_si512(_mm512_and_si512(x, y), _mm512_andnot_si512(x, z)) }
    }

    #[inline]
    fn maj(x: __m512i, y: __m512i, z: __m512i) -> __m512i {
        // Bit i of 0xe8 is one when at least two of the three inputs are one.
        unsafe { _mm512_ternarylogic_epi64::<0xe8>(x, y, z) }
    }

    #[inline]
    fn big_sigma0(x: __m512i) -> __m512i {
        xor3(ror::<28>(x), ror::<34>(x), ror::<39>(x))
    }

    #[inline]
    fn big_sigma1(x: __m512i) -> __m512i {
        xor3(ror::<14>(x), ror::<18>(x), ror::<41>(x))
    }

    #[inline]
    fn small_sigma0(x: __m512i) -> __m512i {
        xor3(ror::<1>(x), ror::<8>(x), unsafe { _mm512_srli_epi64(x, 7) })
    }

    #[inline]
    fn small_sigma1(x: __m512i) -> __m512i {
        xor3(ror::<19>(x), ror::<61>(x), unsafe {
            _mm512_srli_epi64(x, 6)
        })
    }

    #[inline]
    fn xor3(a: __m512i, b: __m512i, c: __m512i) -> __m512i {
        unsafe { _mm512_xor_si512(_mm512_xor_si512(a, b), c) }
    }

    #[inline]
    fn ror<const R: i32>(x: __m512i) -> __m512i {
        unsafe { _mm512_ror_epi64::<R>(x) }
    }

    fn loadu(values: [u64; LANES]) -> __m512i {
        unsafe { _mm512_loadu_si512(values.as_ptr() as *const __m512i) }
    }
    fn storeu(value: __m512i, out: &mut [u64; LANES]) {
        unsafe { _mm512_storeu_si512(out.as_mut_ptr() as *mut __m512i, value) }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn length_trailer_includes_the_high_word() {
            let totals = [
                0,
                1,
                (1 << 61) - 1,
                1 << 61,
                (1 << 61) + 1,
                1 << 62,
                3 << 61,
                1 << 63,
            ];
            let (high, low) = bit_lengths(totals);
            let mut hi = [0; LANES];
            let mut lo = [0; LANES];
            storeu(high, &mut hi);
            storeu(low, &mut lo);
            for lane in 0..LANES {
                assert_eq!(
                    (u128::from(hi[lane]) << 64) | u128::from(lo[lane]),
                    u128::from(totals[lane]) * 8
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_challenge_hashes_match(name: &str, lengths: [usize; SIMD_LANES]) {
        let r = core::array::from_fn(|lane| [(lane as u8).wrapping_mul(17); 32]);
        let public_keys = core::array::from_fn(|lane| [(lane as u8).wrapping_mul(29); 32]);
        let storage: [Vec<u8>; SIMD_LANES] = core::array::from_fn(|lane| {
            (0..lengths[lane])
                .map(|i| (lane as u8).wrapping_mul(41).wrapping_add(i as u8))
                .collect()
        });
        let messages = core::array::from_fn(|lane| storage[lane].as_slice());
        let wide = hash_ed25519_challenges(&r, &public_keys, messages);
        let scalar = core::array::from_fn(|lane| {
            hash_slices(&[&r[lane], &public_keys[lane], storage[lane].as_slice()])
        });
        assert_eq!(wide, scalar, "scenario {name}, lengths {lengths:?}");
    }

    #[test]
    fn every_masked_tail_position_matches_sha2() {
        // The lanes finish in different half-blocks and at different byte positions.
        for offset in 0..64 {
            let lengths = core::array::from_fn(|lane| 64 * lane + (offset + 7 * lane) % 64);
            assert_challenge_hashes_match("masked load", lengths);
        }
    }

    #[test]
    fn avx512_challenge_hash_matches_sha2_across_block_shapes() {
        for len in [
            47usize, 48, 55, 63, 64, 111, 112, 127, 128, 175, 176, 191, 192,
        ] {
            assert_challenge_hashes_match("uniform boundary", [len; SIMD_LANES]);
        }

        for (name, lengths) in [
            ("one block", [0, 1, 7, 19, 30, 40, 46, 47]),
            ("two blocks", [48, 55, 63, 64, 90, 128, 170, 175]),
            ("three blocks", [176, 180, 200, 220, 230, 240, 250, 255]),
            ("five blocks", [496, 500, 510, 520, 530, 540, 550, 558]),
            ("mixed short", [0, 1, 19, 63, 64, 65, 127, 257]),
            (
                "mixed shared prefix",
                [200, 200, 250, 300, 400, 500, 600, 900],
            ),
        ] {
            assert_challenge_hashes_match(name, lengths);
        }
    }
}
