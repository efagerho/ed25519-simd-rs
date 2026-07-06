use crate::batch::SIMD_LANES;

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

/// Scalar SHA-512, kept only as a test reference for the AVX-512 path.
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

/// SIMD SHA-512 of the Ed25519 challenges `SHA512(R || A || M)`.
pub(crate) fn hash_ed25519_challenges(
    r_bytes: &[[u8; 32]; SIMD_LANES],
    public_keys: &[[u8; 32]; SIMD_LANES],
    messages: [&[u8]; SIMD_LANES],
) -> [[u8; 64]; SIMD_LANES] {
    if same_len(messages) {
        avx512::hash_ed25519_challenges(r_bytes, public_keys, messages)
    } else {
        avx512::hash_ed25519_challenges_mixed(r_bytes, public_keys, messages)
    }
}

fn same_len(messages: [&[u8]; SIMD_LANES]) -> bool {
    let len = messages[0].len();
    let mut i = 1;
    while i < SIMD_LANES {
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

    use super::{IV, K, SIMD_LANES};
    use std::arch::x86_64::*;

    const LANES: usize = SIMD_LANES;

    #[derive(Clone, Copy)]
    struct Padding {
        total_len: usize,
        bit_len: u128,
        length_start: usize,
    }

    pub(super) fn hash_ed25519_challenges(
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
                let words =
                    single_block_words(r_bytes, public_keys, messages, message_len, bit_len);
                compress_block(&mut state, words);
                return digests_from_state(state);
            }

            let mut block_index = 0;
            while block_index < block_count {
                let words = block_words(
                    r_bytes,
                    public_keys,
                    messages,
                    total_len,
                    bit_len,
                    block_index,
                    block_count,
                );
                compress_block(&mut state, words);
                block_index += 1;
            }

            digests_from_state(state)
        }
    }

    /// Mixed message lengths, possibly with different SHA-512 block counts.
    /// Blocks that lie entirely within `min_total` (the shortest lane) hold
    /// real data in every lane, so they're bulk-read with no per-lane
    /// branching and no state blending. Once a block runs past the shortest
    /// lane's data, lanes diverge (padding, finalization, or already-finished
    /// lanes holding their digest) and are assembled per-lane, blending
    /// finished lanes' state back in via `active_mask`.
    #[inline(never)]
    pub(super) fn hash_ed25519_challenges_mixed(
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
            let mut min_total = usize::MAX;
            let mut lane = 0;
            while lane < LANES {
                let total_len = 64 + messages[lane].len();
                let block_count = (total_len + 1 + 16).div_ceil(128);
                total_lens[lane] = total_len;
                bit_lens[lane] = (total_len as u128) << 3;
                length_starts[lane] = block_count * 128 - 16;
                block_counts[lane] = block_count;
                max_block_count = core::cmp::max(max_block_count, block_count);
                min_total = core::cmp::min(min_total, total_len);
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
                let block_start = block_index * 128;
                // Every lane's data covers this whole block, so every lane is
                // active here (block_index < block_counts[lane] follows from
                // total_lens[lane] >= min_total >= block_start + 128); skip
                // the mask/blend work that active_mask would otherwise do.
                if block_start == 0 && min_total >= 128 {
                    compress_block(&mut state, first_data_block_words(r_bytes, public_keys, messages));
                } else if block_start >= 128 && block_start + 128 <= min_total {
                    compress_block(&mut state, message_data_block_words(messages, block_start - 64));
                } else {
                    let active = active_mask(&block_counts, block_index);
                    let old_state = state;
                    let words = generic_block_words_mixed(
                        r_bytes,
                        public_keys,
                        messages,
                        &total_lens,
                        &bit_lens,
                        &length_starts,
                        block_index,
                    );
                    compress_block(&mut state, words);
                    if active != 0xff {
                        let mut word = 0;
                        while word < 8 {
                            state[word] =
                                _mm512_mask_blend_epi64(active, old_state[word], state[word]);
                            word += 1;
                        }
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
    #[inline(never)]
    fn single_block_words(
        r_bytes: &[[u8; 32]; LANES],
        public_keys: &[[u8; 32]; LANES],
        messages: [&[u8]; LANES],
        message_len: usize,
        bit_len: u128,
    ) -> [__m512i; 16] {
        debug_assert!(64 + message_len + 1 + 16 <= 128);
        core::array::from_fn(|word| {
            if word == 14 {
                return loadu([0; LANES]);
            }
            if word == 15 {
                return loadu([bit_len as u64; LANES]);
            }

            let mut lanes = [0u64; LANES];
            let mut lane = 0;
            while lane < LANES {
                lanes[lane] = if word < 4 {
                    read_be_u64(&r_bytes[lane], word * 8)
                } else if word < 8 {
                    read_be_u64(&public_keys[lane], (word - 4) * 8)
                } else {
                    let message_offset = (word - 8) * 8;
                    if message_offset + 8 <= message_len {
                        read_be_u64_slice(messages[lane], message_offset)
                    } else {
                        single_block_tail_word(messages[lane], message_len, message_offset)
                    }
                };
                lane += 1;
            }
            loadu(lanes)
        })
    }

    fn single_block_tail_word(message: &[u8], message_len: usize, word_offset: usize) -> u64 {
        let mut bytes = [0u8; 8];
        let mut j = 0;
        while j < 8 {
            let offset = word_offset + j;
            bytes[j] = if offset < message_len {
                message[offset]
            } else if offset == message_len {
                0x80
            } else {
                0
            };
            j += 1;
        }
        u64::from_be_bytes(bytes)
    }

    fn block_words(
        r_bytes: &[[u8; 32]; LANES],
        public_keys: &[[u8; 32]; LANES],
        messages: [&[u8]; LANES],
        total_len: usize,
        bit_len: u128,
        block_index: usize,
        block_count: usize,
    ) -> [__m512i; 16] {
        let block_start = block_index * 128;
        let is_final = block_index + 1 == block_count;

        if block_start >= total_len {
            debug_assert!(is_final);
            return padding_only_block_words(total_len, bit_len, block_start);
        }

        if block_start == 0 {
            if total_len >= 128 {
                return first_data_block_words(r_bytes, public_keys, messages);
            }
            // Block 0 of a two-block hash: R || A || M || 0x80 || zeros; the
            // length words are in the final block.
            return first_block_tail_words(r_bytes, public_keys, messages, total_len - 64);
        }

        // block_start is a multiple of 128 and nonzero, so from here on the
        // block holds only message bytes (message starts at offset 64).
        if block_start + 128 <= total_len {
            return message_data_block_words(messages, block_start - 64);
        }

        let tail_len = total_len - block_start;
        if is_final {
            return final_message_block_words(messages, block_start - 64, tail_len, bit_len);
        }

        // Non-final block where the message ends (tail_len in 112..=127):
        // message tail, 0x80, zeros; the length words are in the next block.
        message_tail_block_words(messages, block_start - 64, tail_len)
    }

    /// Final block containing no message data: zeros, the 0x80 marker when the
    /// data ends exactly at the block boundary, and the length words. The
    /// contents are identical in every lane.
    fn padding_only_block_words(total_len: usize, bit_len: u128, block_start: usize) -> [__m512i; 16] {
        let marker = if block_start == total_len {
            0x80u64 << 56
        } else {
            0
        };
        core::array::from_fn(|word| {
            let value = match word {
                0 => marker,
                14 => (bit_len >> 64) as u64,
                15 => bit_len as u64,
                _ => 0,
            };
            unsafe { _mm512_set1_epi64(value as i64) }
        })
    }

    /// Block 0 when `total_len < 128` (message lengths 48..=63): R and A words
    /// plus the message tail with its 0x80 marker; no length words.
    #[inline(never)]
    fn first_block_tail_words(
        r_bytes: &[[u8; 32]; LANES],
        public_keys: &[[u8; 32]; LANES],
        messages: [&[u8]; LANES],
        message_len: usize,
    ) -> [__m512i; 16] {
        debug_assert!(message_len < 64);
        core::array::from_fn(|word| {
            let mut lanes = [0u64; LANES];
            let mut lane = 0;
            while lane < LANES {
                lanes[lane] = if word < 4 {
                    read_be_u64(&r_bytes[lane], word * 8)
                } else if word < 8 {
                    read_be_u64(&public_keys[lane], (word - 4) * 8)
                } else {
                    let message_offset = (word - 8) * 8;
                    if message_offset + 8 <= message_len {
                        read_be_u64_slice(messages[lane], message_offset)
                    } else {
                        single_block_tail_word(messages[lane], message_len, message_offset)
                    }
                };
                lane += 1;
            }
            loadu(lanes)
        })
    }

    /// Non-final block where the message data ends (`tail_len` in 112..=127):
    /// message bytes, the 0x80 marker, then zeros to the end of the block.
    #[inline(never)]
    fn message_tail_block_words(
        messages: [&[u8]; LANES],
        message_offset: usize,
        tail_len: usize,
    ) -> [__m512i; 16] {
        debug_assert!((112..128).contains(&tail_len));
        core::array::from_fn(|word| {
            let word_offset = word * 8;
            if word_offset > tail_len {
                return loadu([0; LANES]);
            }

            let mut lanes = [0u64; LANES];
            let mut lane = 0;
            while lane < LANES {
                lanes[lane] = if word_offset + 8 <= tail_len {
                    read_be_u64_slice(messages[lane], message_offset + word_offset)
                } else {
                    final_message_tail_word(messages[lane], message_offset, tail_len, word_offset)
                };
                lane += 1;
            }
            loadu(lanes)
        })
    }
    #[inline(never)]
    fn final_message_block_words(
        messages: [&[u8]; LANES],
        message_offset: usize,
        tail_len: usize,
        bit_len: u128,
    ) -> [__m512i; 16] {
        debug_assert!(tail_len <= 111);
        core::array::from_fn(|word| {
            if word == 14 {
                return loadu([(bit_len >> 64) as u64; LANES]);
            }
            if word == 15 {
                return loadu([bit_len as u64; LANES]);
            }

            let word_offset = word * 8;
            if word_offset > tail_len {
                return loadu([0; LANES]);
            }

            let mut lanes = [0u64; LANES];
            let mut lane = 0;
            while lane < LANES {
                lanes[lane] = if word_offset + 8 <= tail_len {
                    read_be_u64_slice(messages[lane], message_offset + word_offset)
                } else {
                    final_message_tail_word(messages[lane], message_offset, tail_len, word_offset)
                };
                lane += 1;
            }
            loadu(lanes)
        })
    }
    fn final_message_tail_word(
        message: &[u8],
        message_offset: usize,
        tail_len: usize,
        word_offset: usize,
    ) -> u64 {
        let mut bytes = [0u8; 8];
        let mut j = 0;
        while j < 8 {
            let offset = word_offset + j;
            bytes[j] = if offset < tail_len {
                message[message_offset + offset]
            } else if offset == tail_len {
                0x80
            } else {
                0
            };
            j += 1;
        }
        u64::from_be_bytes(bytes)
    }
    fn generic_block_words_mixed(
        r_bytes: &[[u8; 32]; LANES],
        public_keys: &[[u8; 32]; LANES],
        messages: [&[u8]; LANES],
        total_lens: &[usize; LANES],
        bit_lens: &[u128; LANES],
        length_starts: &[usize; LANES],
        block_index: usize,
    ) -> [__m512i; 16] {
        let block_start = block_index * 128;
        core::array::from_fn(|word| {
            let mut lanes = [0u64; LANES];
            let word_offset = block_start + word * 8;
            let mut lane = 0;
            while lane < LANES {
                let padding = Padding {
                    total_len: total_lens[lane],
                    bit_len: bit_lens[lane],
                    length_start: length_starts[lane],
                };
                lanes[lane] =
                    mixed_block_word(r_bytes, public_keys, messages, lane, word_offset, padding);
                lane += 1;
            }
            loadu(lanes)
        })
    }

    fn mixed_block_word(
        r_bytes: &[[u8; 32]; LANES],
        public_keys: &[[u8; 32]; LANES],
        messages: [&[u8]; LANES],
        lane: usize,
        word_offset: usize,
        padding: Padding,
    ) -> u64 {
        let word_end = word_offset + 8;
        if word_end <= 32 {
            return read_be_u64(&r_bytes[lane], word_offset);
        }
        if word_offset >= 32 && word_end <= 64 {
            return read_be_u64(&public_keys[lane], word_offset - 32);
        }
        if word_offset >= 64 && word_end <= padding.total_len {
            return read_be_u64_slice(messages[lane], word_offset - 64);
        }
        if word_offset == padding.length_start {
            return (padding.bit_len >> 64) as u64;
        }
        if word_offset == padding.length_start + 8 {
            return padding.bit_len as u64;
        }
        if word_offset > padding.total_len && word_end <= padding.length_start {
            return 0;
        }

        mixed_message_tail_word(messages[lane], word_offset, padding)
    }

    fn mixed_message_tail_word(message: &[u8], word_offset: usize, padding: Padding) -> u64 {
        debug_assert!(word_offset >= 64);
        let mut bytes = [0u8; 8];
        let mut j = 0;
        while j < 8 {
            let offset = word_offset + j;
            bytes[j] = if offset < padding.total_len {
                message[offset - 64]
            } else if offset == padding.total_len {
                0x80
            } else {
                0
            };
            j += 1;
        }
        u64::from_be_bytes(bytes)
    }
    fn first_data_block_words(
        r_bytes: &[[u8; 32]; LANES],
        public_keys: &[[u8; 32]; LANES],
        messages: [&[u8]; LANES],
    ) -> [__m512i; 16] {
        // Only called when the message holds at least 64 bytes (`total_len >=
        // 128`), so this always succeeds; converting once here, rather than
        // per-word below, checks that bound a single time per lane instead of
        // once per word.
        let message_heads: [[u8; 64]; LANES] =
            core::array::from_fn(|lane| messages[lane][..64].try_into().unwrap());
        core::array::from_fn(|word| {
            let mut lanes = [0u64; LANES];
            let mut lane = 0;
            while lane < LANES {
                lanes[lane] = if word < 4 {
                    read_be_u64(&r_bytes[lane], word * 8)
                } else if word < 8 {
                    read_be_u64(&public_keys[lane], (word - 4) * 8)
                } else {
                    read_be_u64(&message_heads[lane], (word - 8) * 8)
                };
                lane += 1;
            }
            loadu(lanes)
        })
    }
    fn message_data_block_words(messages: [&[u8]; LANES], message_offset: usize) -> [__m512i; 16] {
        // Caller guarantees a full 128-byte block is available at
        // `message_offset`; converting once here checks that bound a single
        // time per lane instead of once per word.
        let blocks: [[u8; 128]; LANES] = core::array::from_fn(|lane| {
            messages[lane][message_offset..message_offset + 128]
                .try_into()
                .unwrap()
        });
        core::array::from_fn(|word| {
            let mut lanes = [0u64; LANES];
            let offset = word * 8;
            let mut lane = 0;
            while lane < LANES {
                lanes[lane] = read_be_u64(&blocks[lane], offset);
                lane += 1;
            }
            loadu(lanes)
        })
    }

    // A `&[u8; N]` (as opposed to `&[u8]`) keeps the bound `offset + 8 <= N`
    // checkable against a monomorphized-in constant instead of a runtime
    // slice length, so the compiler can fold or cheapen it. Callers touching a
    // fixed-size window (a 32-byte key/R, or a pre-sliced whole message block)
    // should convert to an array reference once and read through this; callers
    // stuck with a genuinely variable-length remainder use `read_be_u64_slice`.
    #[inline(always)]
    fn read_be_u64<const N: usize>(bytes: &[u8; N], offset: usize) -> u64 {
        u64::from_be_bytes(bytes[offset..offset + 8].try_into().unwrap())
    }

    #[inline(always)]
    fn read_be_u64_slice(bytes: &[u8], offset: usize) -> u64 {
        u64::from_be_bytes(bytes[offset..offset + 8].try_into().unwrap())
    }

    fn compress_block(state: &mut [__m512i; 8], block_words: [__m512i; 16]) {
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
    fn rfc4634_multiblock_hash() {
        assert_eq!(
            hash_slices(&[concat!(
                "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn",
                "hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"
            )
            .as_bytes()]),
            hex(
                "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb688901\
                 8501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909"
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

        let wide = hash_ed25519_challenges(&r, &public_keys, messages);
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

        let wide = hash_ed25519_challenges(&r, &public_keys, messages);
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

        let wide = hash_ed25519_challenges(&r, &public_keys, messages);
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
    fn avx512_challenge_hash_matches_scalar_at_boundary_lengths() {
        // One uniform-length hash per length, covering every block-builder
        // branch: single block (47), block 0 with tail (48, 55, 63), padding-only
        // final block with the 0x80 marker at the boundary (64, 192), final
        // message tails (111, 112, 127, 128, 175), and a non-final block where
        // the message ends (176, 191).
        let lengths = [47usize, 48, 55, 63, 64, 111, 112, 127, 128, 175, 176, 191, 192];
        let storage: [[u8; 192]; 8] = core::array::from_fn(|lane| {
            core::array::from_fn(|i| (lane as u8).wrapping_mul(31).wrapping_add(i as u8))
        });

        for len in lengths {
            let r = core::array::from_fn(|lane| [(lane as u8).wrapping_add(len as u8); 32]);
            let public_keys = core::array::from_fn(|lane| [(lane as u8).wrapping_mul(37); 32]);
            let messages = core::array::from_fn(|lane| &storage[lane][..len]);

            let wide = hash_ed25519_challenges(&r, &public_keys, messages);
            let scalar = core::array::from_fn(|lane| {
                hash_slices(&[&r[lane], &public_keys[lane], &storage[lane][..len]])
            });
            assert_eq!(wide, scalar, "length {len}");
        }
    }

    #[test]
    fn avx512_challenge_hash_matches_scalar_with_uniform_block_counts() {
        // Mixed lengths that share one block count, per count 1..=3 and a
        // larger one with bulk interior blocks; exercises the shared-prefix
        // bulk read (min_total reaches every lane's final block) including
        // divergent block 0 (two-block hashes) and tails.
        let length_sets: [[usize; 8]; 4] = [
            [0, 1, 7, 19, 30, 40, 46, 47],          // 1 block
            [48, 55, 63, 64, 90, 128, 170, 175],    // 2 blocks
            [176, 180, 200, 220, 230, 240, 250, 255], // 3 blocks
            [496, 500, 510, 520, 530, 540, 550, 558], // 5 blocks
        ];
        let storage: [[u8; 558]; 8] = core::array::from_fn(|lane| {
            core::array::from_fn(|i| (lane as u8).wrapping_mul(41).wrapping_add(i as u8))
        });

        for lengths in length_sets {
            let r = core::array::from_fn(|lane| [(lane as u8).wrapping_add(51); 32]);
            let public_keys = core::array::from_fn(|lane| [(lane as u8).wrapping_mul(53); 32]);
            let messages = core::array::from_fn(|lane| &storage[lane][..lengths[lane]]);

            let wide = hash_ed25519_challenges(&r, &public_keys, messages);
            let scalar = core::array::from_fn(|lane| {
                hash_slices(&[&r[lane], &public_keys[lane], &storage[lane][..lengths[lane]]])
            });
            assert_eq!(wide, scalar, "lengths {lengths:?}");
        }
    }

    #[test]
    fn avx512_challenge_hash_matches_scalar_with_shared_prefix_and_different_block_counts() {
        // Lengths spanning several distinct block counts but with a long
        // common prefix, so min_total reaches well past block 0: this is the
        // case a same-block-count bucketing pass cannot help with, but the
        // shared-prefix bulk read still applies to the blocks before the
        // shortest lane's data ends.
        let lengths = [200usize, 200, 250, 300, 400, 500, 600, 900];
        let storage: [[u8; 900]; 8] = core::array::from_fn(|lane| {
            core::array::from_fn(|i| (lane as u8).wrapping_mul(43).wrapping_add(i as u8))
        });
        let r = core::array::from_fn(|lane| [(lane as u8).wrapping_add(61); 32]);
        let public_keys = core::array::from_fn(|lane| [(lane as u8).wrapping_mul(67); 32]);
        let messages = core::array::from_fn(|lane| &storage[lane][..lengths[lane]]);

        let wide = hash_ed25519_challenges(&r, &public_keys, messages);
        let scalar = core::array::from_fn(|lane| {
            hash_slices(&[&r[lane], &public_keys[lane], &storage[lane][..lengths[lane]]])
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

        let wide = hash_ed25519_challenges(&r, &public_keys, messages);
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
