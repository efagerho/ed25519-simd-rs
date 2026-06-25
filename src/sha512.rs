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

/// Scalar SHA-512 — kept only as a test reference for the 8-wide AVX-512 path.
#[cfg(test)]
#[derive(Clone)]
struct Sha512 {
    state: [u64; 8],
    buffer: [u8; 128],
    buffer_len: usize,
    len_bytes: u128,
}

#[cfg(test)]
impl Sha512 {
    fn new() -> Self {
        Self {
            state: IV,
            buffer: [0; 128],
            buffer_len: 0,
            len_bytes: 0,
        }
    }

    fn update(&mut self, mut input: &[u8]) {
        self.len_bytes += input.len() as u128;

        if self.buffer_len != 0 {
            let take = core::cmp::min(128 - self.buffer_len, input.len());
            self.buffer[self.buffer_len..self.buffer_len + take].copy_from_slice(&input[..take]);
            self.buffer_len += take;
            input = &input[take..];
            if self.buffer_len == 128 {
                compress(&mut self.state, &self.buffer);
                self.buffer_len = 0;
            }
        }

        while input.len() >= 128 {
            let mut block = [0u8; 128];
            block.copy_from_slice(&input[..128]);
            compress(&mut self.state, &block);
            input = &input[128..];
        }

        if !input.is_empty() {
            self.buffer[..input.len()].copy_from_slice(input);
            self.buffer_len = input.len();
        }
    }

    fn finalize(mut self) -> [u8; 64] {
        self.buffer[self.buffer_len] = 0x80;
        self.buffer_len += 1;

        if self.buffer_len > 112 {
            let mut i = self.buffer_len;
            while i < 128 {
                self.buffer[i] = 0;
                i += 1;
            }
            compress(&mut self.state, &self.buffer);
            self.buffer_len = 0;
        }

        let mut i = self.buffer_len;
        while i < 112 {
            self.buffer[i] = 0;
            i += 1;
        }

        let bit_len = self.len_bytes << 3;
        self.buffer[112..128].copy_from_slice(&bit_len.to_be_bytes());
        compress(&mut self.state, &self.buffer);

        let mut out = [0u8; 64];
        let mut i = 0;
        while i < 8 {
            out[i * 8..i * 8 + 8].copy_from_slice(&self.state[i].to_be_bytes());
            i += 1;
        }
        out
    }
}

#[cfg(test)]
pub(crate) fn hash_slices(slices: &[&[u8]]) -> [u8; 64] {
    let mut h = Sha512::new();
    let mut i = 0;
    while i < slices.len() {
        h.update(slices[i]);
        i += 1;
    }
    h.finalize()
}

/// 8-wide SHA-512 of the Ed25519 challenges `SHA512(R || A || M)`.
pub(crate) fn hash_ed25519_challenges8(
    r_bytes: &[[u8; 32]; 8],
    public_keys: &[[u8; 32]; 8],
    messages: [&[u8]; 8],
) -> [[u8; 64]; 8] {
    if same_len(messages) {
        avx512::hash_ed25519_challenges8(r_bytes, public_keys, messages)
    } else {
        avx512::hash_ed25519_challenges8_mixed(r_bytes, public_keys, messages)
    }
}

fn same_len(messages: [&[u8]; 8]) -> bool {
    let len = messages[0].len();
    let mut i = 1;
    while i < 8 {
        if messages[i].len() != len {
            return false;
        }
        i += 1;
    }
    true
}

#[cfg(test)]
fn compress(state: &mut [u64; 8], block: &[u8; 128]) {
    let mut w = [0u64; 80];
    let mut i = 0;
    while i < 16 {
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&block[i * 8..i * 8 + 8]);
        w[i] = u64::from_be_bytes(bytes);
        i += 1;
    }
    while i < 80 {
        w[i] = small_sigma1(w[i - 2])
            .wrapping_add(w[i - 7])
            .wrapping_add(small_sigma0(w[i - 15]))
            .wrapping_add(w[i - 16]);
        i += 1;
    }

    let mut a = state[0];
    let mut b = state[1];
    let mut c = state[2];
    let mut d = state[3];
    let mut e = state[4];
    let mut f = state[5];
    let mut g = state[6];
    let mut h = state[7];

    i = 0;
    while i < 80 {
        let t1 = h
            .wrapping_add(big_sigma1(e))
            .wrapping_add(ch(e, f, g))
            .wrapping_add(K[i])
            .wrapping_add(w[i]);
        let t2 = big_sigma0(a).wrapping_add(maj(a, b, c));
        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
        i += 1;
    }

    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
}

#[cfg(test)]
fn ch(x: u64, y: u64, z: u64) -> u64 {
    (x & y) ^ (!x & z)
}

#[cfg(test)]
fn maj(x: u64, y: u64, z: u64) -> u64 {
    (x & y) ^ (x & z) ^ (y & z)
}

#[cfg(test)]
fn big_sigma0(x: u64) -> u64 {
    x.rotate_right(28) ^ x.rotate_right(34) ^ x.rotate_right(39)
}

#[cfg(test)]
fn big_sigma1(x: u64) -> u64 {
    x.rotate_right(14) ^ x.rotate_right(18) ^ x.rotate_right(41)
}

#[cfg(test)]
fn small_sigma0(x: u64) -> u64 {
    x.rotate_right(1) ^ x.rotate_right(8) ^ (x >> 7)
}

#[cfg(test)]
fn small_sigma1(x: u64) -> u64 {
    x.rotate_right(19) ^ x.rotate_right(61) ^ (x >> 6)
}

mod avx512 {
    use core::mem::MaybeUninit;

    use super::{IV, K};
    use std::arch::x86_64::*;

    const LANES: usize = 8;

    #[derive(Clone, Copy)]
    struct Padding {
        total_len: usize,
        bit_len: u128,
        length_start: usize,
    }

    pub(super) fn hash_ed25519_challenges8(
        r_bytes: &[[u8; 32]; LANES],
        public_keys: &[[u8; 32]; LANES],
        messages: [&[u8]; LANES],
    ) -> [[u8; 64]; LANES] {
        unsafe {
            let message_len = messages[0].len();
            let total_len = 64 + message_len;
            let block_count = (total_len + 1 + 16).div_ceil(128);

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

            let bit_len = (total_len as u128) << 3;
            if block_count == 1 {
                let words = generic_block_words8(
                    r_bytes,
                    public_keys,
                    messages,
                    total_len,
                    bit_len,
                    0,
                    block_count,
                );
                compress8(&mut state, words);
                return digests_from_state(state);
            }

            let mut block_index = 0;
            while block_index < block_count {
                let words = block_words8(
                    r_bytes,
                    public_keys,
                    messages,
                    total_len,
                    bit_len,
                    block_index,
                    block_count,
                );
                compress8(&mut state, words);
                block_index += 1;
            }

            digests_from_state(state)
        }
    }

    #[inline(never)]
    pub(super) fn hash_ed25519_challenges8_mixed(
        r_bytes: &[[u8; 32]; LANES],
        public_keys: &[[u8; 32]; LANES],
        messages: [&[u8]; LANES],
    ) -> [[u8; 64]; LANES] {
        unsafe {
            let mut total_lens = [0usize; LANES];
            let mut bit_lens = [0u128; LANES];
            let mut length_starts = [0usize; LANES];
            let mut block_counts = [0usize; LANES];
            let mut max_block_count = 0usize;
            let mut lane = 0;
            while lane < LANES {
                let total_len = 64 + messages[lane].len();
                let block_count = (total_len + 1 + 16).div_ceil(128);
                total_lens[lane] = total_len;
                bit_lens[lane] = (total_len as u128) << 3;
                length_starts[lane] = block_count * 128 - 16;
                block_counts[lane] = block_count;
                max_block_count = core::cmp::max(max_block_count, block_count);
                lane += 1;
            }

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

            let mut block_index = 0;
            while block_index < max_block_count {
                let active = active_mask(&block_counts, block_index);
                let old_state = state;
                let words = generic_block_words8_mixed(
                    r_bytes,
                    public_keys,
                    messages,
                    &total_lens,
                    &bit_lens,
                    &length_starts,
                    block_index,
                );
                compress8(&mut state, words);
                if active != 0xff {
                    let mut word = 0;
                    while word < 8 {
                        state[word] = _mm512_mask_blend_epi64(active, old_state[word], state[word]);
                        word += 1;
                    }
                }
                block_index += 1;
            }

            digests_from_state(state)
        }
    }

    fn active_mask(block_counts: &[usize; LANES], block_index: usize) -> __mmask8 {
        let mut mask = 0u8;
        let mut lane = 0;
        while lane < LANES {
            if block_index < block_counts[lane] {
                mask |= 1 << lane;
            }
            lane += 1;
        }
        mask as __mmask8
    }
    fn block_words8(
        r_bytes: &[[u8; 32]; LANES],
        public_keys: &[[u8; 32]; LANES],
        messages: [&[u8]; LANES],
        total_len: usize,
        bit_len: u128,
        block_index: usize,
        block_count: usize,
    ) -> [__m512i; 16] {
        let block_start = block_index * 128;
        if block_start == 0 && total_len >= 128 {
            return first_data_block_words8(r_bytes, public_keys, messages);
        }

        if block_start >= 64 && block_start + 128 <= total_len {
            return message_data_block_words8(messages, block_start - 64);
        }

        generic_block_words8(
            r_bytes,
            public_keys,
            messages,
            total_len,
            bit_len,
            block_index,
            block_count,
        )
    }
    fn generic_block_words8(
        r_bytes: &[[u8; 32]; LANES],
        public_keys: &[[u8; 32]; LANES],
        messages: [&[u8]; LANES],
        total_len: usize,
        bit_len: u128,
        block_index: usize,
        block_count: usize,
    ) -> [__m512i; 16] {
        let length_start = block_count * 128 - 16;
        let padding = Padding {
            total_len,
            bit_len,
            length_start,
        };
        core::array::from_fn(|word| {
            let mut lanes = [0u64; LANES];
            let mut lane = 0;
            while lane < LANES {
                let mut bytes = [0u8; 8];
                let mut j = 0;
                while j < 8 {
                    let offset = block_index * 128 + word * 8 + j;
                    bytes[j] = message_byte(r_bytes, public_keys, messages, lane, offset, padding);
                    j += 1;
                }
                lanes[lane] = u64::from_be_bytes(bytes);
                lane += 1;
            }
            loadu(lanes)
        })
    }
    fn generic_block_words8_mixed(
        r_bytes: &[[u8; 32]; LANES],
        public_keys: &[[u8; 32]; LANES],
        messages: [&[u8]; LANES],
        total_lens: &[usize; LANES],
        bit_lens: &[u128; LANES],
        length_starts: &[usize; LANES],
        block_index: usize,
    ) -> [__m512i; 16] {
        core::array::from_fn(|word| {
            let mut lanes = [0u64; LANES];
            let mut lane = 0;
            while lane < LANES {
                let mut bytes = [0u8; 8];
                let padding = Padding {
                    total_len: total_lens[lane],
                    bit_len: bit_lens[lane],
                    length_start: length_starts[lane],
                };
                let mut j = 0;
                while j < 8 {
                    let offset = block_index * 128 + word * 8 + j;
                    bytes[j] = message_byte(r_bytes, public_keys, messages, lane, offset, padding);
                    j += 1;
                }
                lanes[lane] = u64::from_be_bytes(bytes);
                lane += 1;
            }
            loadu(lanes)
        })
    }
    fn first_data_block_words8(
        r_bytes: &[[u8; 32]; LANES],
        public_keys: &[[u8; 32]; LANES],
        messages: [&[u8]; LANES],
    ) -> [__m512i; 16] {
        core::array::from_fn(|word| {
            let mut lanes = [0u64; LANES];
            let mut lane = 0;
            while lane < LANES {
                lanes[lane] = if word < 4 {
                    read_be_u64(r_bytes[lane].as_ptr(), word * 8)
                } else if word < 8 {
                    read_be_u64(public_keys[lane].as_ptr(), (word - 4) * 8)
                } else {
                    read_be_u64(messages[lane].as_ptr(), (word - 8) * 8)
                };
                lane += 1;
            }
            loadu(lanes)
        })
    }
    fn message_data_block_words8(messages: [&[u8]; LANES], message_offset: usize) -> [__m512i; 16] {
        core::array::from_fn(|word| {
            let mut lanes = [0u64; LANES];
            let offset = message_offset + word * 8;
            let mut lane = 0;
            while lane < LANES {
                lanes[lane] = read_be_u64(messages[lane].as_ptr(), offset);
                lane += 1;
            }
            loadu(lanes)
        })
    }

    #[inline(always)]
    fn read_be_u64(bytes: *const u8, offset: usize) -> u64 {
        unsafe { u64::from_be(core::ptr::read_unaligned(bytes.add(offset) as *const u64)) }
    }

    fn message_byte(
        r_bytes: &[[u8; 32]; LANES],
        public_keys: &[[u8; 32]; LANES],
        messages: [&[u8]; LANES],
        lane: usize,
        offset: usize,
        padding: Padding,
    ) -> u8 {
        if offset < 32 {
            r_bytes[lane][offset]
        } else if offset < 64 {
            public_keys[lane][offset - 32]
        } else if offset < padding.total_len {
            messages[lane][offset - 64]
        } else if offset == padding.total_len {
            0x80
        } else if offset >= padding.length_start && offset < padding.length_start + 16 {
            let length_bytes = padding.bit_len.to_be_bytes();
            length_bytes[offset - padding.length_start]
        } else {
            0
        }
    }
    fn compress8(state: &mut [__m512i; 8], block_words: [__m512i; 16]) {
        unsafe {
            let mut w: [MaybeUninit<__m512i>; 80] = MaybeUninit::uninit().assume_init();
            let mut i = 0;
            while i < 16 {
                w[i].write(block_words[i]);
                i += 1;
            }
            while i < 80 {
                let word = add4(
                    small_sigma1(read_schedule_word(&w, i - 2)),
                    read_schedule_word(&w, i - 7),
                    small_sigma0(read_schedule_word(&w, i - 15)),
                    read_schedule_word(&w, i - 16),
                );
                w[i].write(word);
                i += 1;
            }

            let mut a = state[0];
            let mut b = state[1];
            let mut c = state[2];
            let mut d = state[3];
            let mut e = state[4];
            let mut f = state[5];
            let mut g = state[6];
            let mut h = state[7];

            i = 0;
            while i < 80 {
                let t1 = add5(
                    h,
                    big_sigma1(e),
                    ch(e, f, g),
                    _mm512_set1_epi64(K[i] as i64),
                    read_schedule_word(&w, i),
                );
                let t2 = add(big_sigma0(a), maj(a, b, c));
                h = g;
                g = f;
                f = e;
                e = add(d, t1);
                d = c;
                c = b;
                b = a;
                a = add(t1, t2);
                i += 1;
            }

            state[0] = add(state[0], a);
            state[1] = add(state[1], b);
            state[2] = add(state[2], c);
            state[3] = add(state[3], d);
            state[4] = add(state[4], e);
            state[5] = add(state[5], f);
            state[6] = add(state[6], g);
            state[7] = add(state[7], h);
        }
    }

    #[inline(always)]
    fn read_schedule_word(w: &[MaybeUninit<__m512i>; 80], index: usize) -> __m512i {
        unsafe { w[index].assume_init() }
    }
    fn digests_from_state(state: [__m512i; 8]) -> [[u8; 64]; LANES] {
        let mut words = [[0u64; LANES]; 8];
        let mut word = 0;
        while word < 8 {
            storeu(state[word], &mut words[word]);
            word += 1;
        }

        core::array::from_fn(|lane| {
            let mut digest = [0u8; 64];
            let mut word = 0;
            while word < 8 {
                digest[word * 8..word * 8 + 8].copy_from_slice(&words[word][lane].to_be_bytes());
                word += 1;
            }
            digest
        })
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
    fn add5(a: __m512i, b: __m512i, c: __m512i, d: __m512i, e: __m512i) -> __m512i {
        add(add4(a, b, c, d), e)
    }

    #[inline]
    fn ch(x: __m512i, y: __m512i, z: __m512i) -> __m512i {
        unsafe { _mm512_xor_si512(_mm512_and_si512(x, y), _mm512_andnot_si512(x, z)) }
    }

    #[inline]
    fn maj(x: __m512i, y: __m512i, z: __m512i) -> __m512i {
        unsafe {
            _mm512_xor_si512(
                _mm512_xor_si512(_mm512_and_si512(x, y), _mm512_and_si512(x, z)),
                _mm512_and_si512(y, z),
            )
        }
    }

    #[inline]
    fn big_sigma0(x: __m512i) -> __m512i {
        xor3(ror::<28, 36>(x), ror::<34, 30>(x), ror::<39, 25>(x))
    }

    #[inline]
    fn big_sigma1(x: __m512i) -> __m512i {
        xor3(ror::<14, 50>(x), ror::<18, 46>(x), ror::<41, 23>(x))
    }

    #[inline]
    fn small_sigma0(x: __m512i) -> __m512i {
        xor3(ror::<1, 63>(x), ror::<8, 56>(x), unsafe {
            _mm512_srli_epi64(x, 7)
        })
    }

    #[inline]
    fn small_sigma1(x: __m512i) -> __m512i {
        xor3(ror::<19, 45>(x), ror::<61, 3>(x), unsafe {
            _mm512_srli_epi64(x, 6)
        })
    }

    #[inline]
    fn xor3(a: __m512i, b: __m512i, c: __m512i) -> __m512i {
        unsafe { _mm512_xor_si512(_mm512_xor_si512(a, b), c) }
    }

    #[inline]
    fn ror<const R: u32, const L: u32>(x: __m512i) -> __m512i {
        unsafe { _mm512_or_si512(_mm512_srli_epi64::<R>(x), _mm512_slli_epi64::<L>(x)) }
    }
    fn loadu(values: [u64; LANES]) -> __m512i {
        unsafe { _mm512_loadu_si512(values.as_ptr() as *const __m512i) }
    }
    fn storeu(value: __m512i, out: &mut [u64; LANES]) {
        unsafe { _mm512_storeu_si512(out.as_mut_ptr() as *mut __m512i, value) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex<const N: usize>(s: &str) -> [u8; N] {
        let mut out = [0u8; N];
        let bytes = s.as_bytes();
        let mut i = 0;
        while i < N {
            out[i] = (nibble(bytes[i * 2]) << 4) | nibble(bytes[i * 2 + 1]);
            i += 1;
        }
        out
    }

    fn nibble(b: u8) -> u8 {
        match b {
            b'0'..=b'9' => b - b'0',
            b'a'..=b'f' => b - b'a' + 10,
            _ => panic!("bad hex"),
        }
    }

    #[test]
    fn empty_hash() {
        assert_eq!(
            hash_slices(&[b""]),
            hex(
                "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce\
                 47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
            )
        );
    }

    #[test]
    fn abc_hash() {
        assert_eq!(
            hash_slices(&[b"abc"]),
            hex(
                "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a\
                 2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
            )
        );
    }

    #[test]
    fn avx512_challenge_hash_matches_scalar() {
        let r = core::array::from_fn(|lane| [lane as u8; 32]);
        let public_keys = core::array::from_fn(|lane| [(lane as u8).wrapping_mul(3); 32]);
        let messages_storage: [[u8; 19]; 8] = core::array::from_fn(|lane| {
            core::array::from_fn(|i| (lane as u8).wrapping_mul(17).wrapping_add(i as u8))
        });
        let messages = core::array::from_fn(|lane| messages_storage[lane].as_slice());

        let wide = hash_ed25519_challenges8(&r, &public_keys, messages);
        let scalar = core::array::from_fn(|lane| {
            hash_slices(&[
                &r[lane],
                &public_keys[lane],
                messages_storage[lane].as_slice(),
            ])
        });
        assert_eq!(wide, scalar);
    }

    #[test]
    fn avx512_challenge_hash_matches_scalar_with_spilled_padding() {
        let r = core::array::from_fn(|lane| [(lane as u8).wrapping_add(9); 32]);
        let public_keys = core::array::from_fn(|lane| [(lane as u8).wrapping_mul(5); 32]);
        let messages_storage: [[u8; 64]; 8] = core::array::from_fn(|lane| {
            core::array::from_fn(|i| (lane as u8).wrapping_mul(11).wrapping_add(i as u8))
        });
        let messages = core::array::from_fn(|lane| messages_storage[lane].as_slice());

        let wide = hash_ed25519_challenges8(&r, &public_keys, messages);
        let scalar = core::array::from_fn(|lane| {
            hash_slices(&[
                &r[lane],
                &public_keys[lane],
                messages_storage[lane].as_slice(),
            ])
        });
        assert_eq!(wide, scalar);
    }

    #[test]
    fn avx512_challenge_hash_matches_scalar_with_full_message_blocks() {
        let r = core::array::from_fn(|lane| [(lane as u8).wrapping_add(13); 32]);
        let public_keys = core::array::from_fn(|lane| [(lane as u8).wrapping_mul(7); 32]);
        let messages_storage: [[u8; 257]; 8] = core::array::from_fn(|lane| {
            core::array::from_fn(|i| (lane as u8).wrapping_mul(19).wrapping_add(i as u8))
        });
        let messages = core::array::from_fn(|lane| messages_storage[lane].as_slice());

        let wide = hash_ed25519_challenges8(&r, &public_keys, messages);
        let scalar = core::array::from_fn(|lane| {
            hash_slices(&[
                &r[lane],
                &public_keys[lane],
                messages_storage[lane].as_slice(),
            ])
        });
        assert_eq!(wide, scalar);
    }

    #[test]
    fn avx512_challenge_hash_matches_scalar_with_mixed_lengths() {
        let r = core::array::from_fn(|lane| [(lane as u8).wrapping_add(21); 32]);
        let public_keys = core::array::from_fn(|lane| [(lane as u8).wrapping_mul(23); 32]);
        let messages_storage: [[u8; 257]; 8] = core::array::from_fn(|lane| {
            core::array::from_fn(|i| (lane as u8).wrapping_mul(29).wrapping_add(i as u8))
        });
        let lengths = [0usize, 1, 19, 63, 64, 65, 127, 257];
        let messages = core::array::from_fn(|lane| &messages_storage[lane][..lengths[lane]]);

        let wide = hash_ed25519_challenges8(&r, &public_keys, messages);
        let scalar = core::array::from_fn(|lane| {
            hash_slices(&[
                &r[lane],
                &public_keys[lane],
                &messages_storage[lane][..lengths[lane]],
            ])
        });
        assert_eq!(wide, scalar);
    }
}
