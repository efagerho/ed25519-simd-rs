use crate::batch::{R_ENCODING_LEN, SIMD_LANES};
use crate::input::PUBLIC_KEY_LEN;
use core::mem::MaybeUninit;

#[cfg(not(test))]
core::arch::global_asm!(include_str!("sha512.S"), options(raw));
#[cfg(test)]
core::arch::global_asm!(
    ".set .Lsha512_test, 1",
    include_str!("sha512.S"),
    options(raw)
);

const _: () = assert!(SIMD_LANES == 8 && R_ENCODING_LEN == 32 && PUBLIC_KEY_LEN == 32);

unsafe extern "C" {
    fn ed25519_simd_sha512_challenge(
        out: *mut [[u64; SIMD_LANES]; 8],
        r: &[[u8; R_ENCODING_LEN]; SIMD_LANES],
        keys: &[[u8; PUBLIC_KEY_LEN]; SIMD_LANES],
        messages: &[*const u8; SIMD_LANES],
        lengths: &[usize; SIMD_LANES],
    );
}

/// Eight SHA-512(R || A || M) digests in the scalar reducer's word-major layout.
pub(crate) fn hash_ed25519_challenge_words(
    r_bytes: &[[u8; R_ENCODING_LEN]; SIMD_LANES],
    public_keys: &[[u8; PUBLIC_KEY_LEN]; SIMD_LANES],
    messages: [&[u8]; SIMD_LANES],
) -> [[u64; SIMD_LANES]; 8] {
    let pointers = messages.map(<[u8]>::as_ptr);
    let lengths = messages.map(<[u8]>::len);
    let mut words = MaybeUninit::uninit();
    // SAFETY: each pointer and length comes from the same live slice. The
    // assembly writes all eight words of every lane to the disjoint output.
    unsafe {
        ed25519_simd_sha512_challenge(
            words.as_mut_ptr(),
            r_bytes,
            public_keys,
            &pointers,
            &lengths,
        );
        words.assume_init()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::{Digest, Sha512};

    fn assert_digests(
        name: &str,
        words: &[[u64; SIMD_LANES]; 8],
        r: &[[u8; 32]; SIMD_LANES],
        keys: &[[u8; 32]; SIMD_LANES],
        messages: [&[u8]; SIMD_LANES],
    ) {
        for lane in 0..SIMD_LANES {
            let mut reference = Sha512::new();
            reference.update(r[lane]);
            reference.update(keys[lane]);
            reference.update(messages[lane]);
            let digest: [u8; 64] = reference.finalize().into();
            for (word, bytes) in digest.as_chunks::<8>().0.iter().enumerate() {
                assert_eq!(
                    words[word][lane].to_le_bytes(),
                    *bytes,
                    "{name}, lane {lane}, word {word}, message length {}",
                    messages[lane].len()
                );
            }
        }
    }

    #[test]
    fn length_trailer_includes_the_high_word() {
        unsafe extern "C" {
            fn ed25519_simd_test_sha512_lengths(out: &mut [[u64; 8]; 3], lengths: &[usize; 8]);
        }
        let lengths = [
            0,
            47,
            48,
            (1 << 61) - 65,
            (1 << 61) - 64,
            1 << 61,
            1 << 62,
            isize::MAX as usize,
        ];
        let mut rows = [[0; 8]; 3];
        unsafe { ed25519_simd_test_sha512_lengths(&mut rows, &lengths) };
        for (lane, len) in lengths.into_iter().enumerate() {
            let bits = (len as u128 + 64) * 8;
            assert_eq!(
                (u128::from(rows[0][lane]) << 64) | u128::from(rows[1][lane]),
                bits
            );
            assert_eq!(
                rows[2][lane] as usize + 1,
                crate::batch::challenge_block_count(len)
            );
        }
    }

    fn assert_challenge_hashes_match(name: &str, lengths: [usize; SIMD_LANES]) {
        let r = core::array::from_fn(|lane| core::array::from_fn(|i| (lane * 17 + i) as u8));
        let public_keys =
            core::array::from_fn(|lane| core::array::from_fn(|i| (lane * 29 + 3 * i) as u8));
        let storage: [Vec<u8>; SIMD_LANES] = core::array::from_fn(|lane| {
            (0..lengths[lane])
                .map(|i| (lane as u8).wrapping_mul(41).wrapping_add(i as u8))
                .collect()
        });
        let messages = core::array::from_fn(|lane| storage[lane].as_slice());
        let words = hash_ed25519_challenge_words(&r, &public_keys, messages);
        assert_digests(name, &words, &r, &public_keys, messages);
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
    fn respects_guard_pages_for_prefixes_messages_and_digests() {
        use crate::test_support::GuardedPage;

        let input = GuardedPage::new();
        let output = GuardedPage::new();
        for end in [false, true] {
            let bytes = unsafe { core::slice::from_raw_parts_mut(input.buffer(512, end), 512) };
            for (i, byte) in bytes.iter_mut().enumerate() {
                *byte = (i * 17 + usize::from(end)) as u8;
            }
        }
        input.read_only();
        for end in [false, true] {
            // All inputs share a read-only page. In particular, an empty tail
            // can point to the inaccessible page immediately after the input.
            let r = unsafe { &*input.buffer(256, end).cast::<[[u8; 32]; 8]>() };
            let keys = unsafe { &*input.buffer(256, !end).cast::<[[u8; 32]; 8]>() };
            let out = output.buffer(512, end).cast::<[[u64; 8]; 8]>();
            for tail in 0..64 {
                let lengths = [
                    0,
                    tail,
                    64 + tail,
                    128 + tail,
                    192 + tail,
                    256 + tail,
                    320 + tail,
                    384 + tail,
                ];
                let messages = lengths
                    .map(|len| unsafe { core::slice::from_raw_parts(input.buffer(len, end), len) });
                let pointers = messages.map(<[u8]>::as_ptr);
                let words = unsafe {
                    out.write([[u64::MAX; 8]; 8]);
                    ed25519_simd_sha512_challenge(out, r, keys, &pointers, &lengths);
                    out.read()
                };
                assert_digests("guarded", &words, r, keys, messages);
            }
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
