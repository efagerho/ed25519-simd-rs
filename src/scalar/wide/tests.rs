use super::tests::{L_BYTES, reference_radix16};
use super::*;
use core::mem::MaybeUninit;
use rand::{RngCore, SeedableRng, rngs::StdRng};

#[path = "native.rs"]
mod native;

const WIDE_WORDS: usize = 8;
type DigestWords = [[u64; LANES]; WIDE_WORDS];
type ScalarLimbs = [[u64; LANES]; 5];

unsafe extern "C" {
    fn ed25519_simd_digest_to_radix16(out: *mut u8, words: *const u8);

    fn ed25519_simd_scalar_reduce_ifma(out: *mut u8, words: *const u8);
}

fn wide_words_to_radix16(words: &[[u64; LANES]; WIDE_WORDS]) -> [Radix16; LANES] {
    let mut out = MaybeUninit::<[Radix16; LANES]>::uninit();
    // The pointers cover disjoint 512-byte buffers. The assembly accepts
    // unaligned addresses and writes all 64 digit bytes in every lane.
    unsafe {
        ed25519_simd_digest_to_radix16(out.as_mut_ptr().cast(), words.as_ptr().cast());
        out.assume_init()
    }
}

fn reduce(words: &DigestWords) -> ScalarLimbs {
    let mut out = core::mem::MaybeUninit::<ScalarLimbs>::uninit();
    // SAFETY: the reducer reads all 512 input bytes and writes all 320
    // output bytes. Both buffers can be unaligned and are disjoint.
    unsafe {
        ed25519_simd_scalar_reduce_ifma(out.as_mut_ptr().cast(), words.as_ptr().cast());
        out.assume_init()
    }
}

fn reference_bytes(words: &DigestWords) -> [[u8; 32]; LANES] {
    core::array::from_fn(|lane| {
        let input = core::array::from_fn(|i| words[i / 8][lane].to_le_bytes()[i % 8]);
        curve25519::scalar::Scalar::from_bytes_mod_order_wide(&input).to_bytes()
    })
}

fn reference_limbs(bytes: &[[u8; 32]; LANES]) -> ScalarLimbs {
    core::array::from_fn(|row| {
        core::array::from_fn(|lane| {
            let start = row * 52;
            (start..(start + 52).min(256)).fold(0, |limb, i| {
                limb | (u64::from((bytes[lane][i / 8] >> (i % 8)) & 1) << (i - start))
            })
        })
    })
}

fn neighbors(value: [u64; WIDE_WORDS]) -> [[u64; WIDE_WORDS]; 3] {
    let mut below = value;
    for word in &mut below {
        let (next, borrow) = word.overflowing_sub(1);
        *word = next;
        if !borrow {
            break;
        }
    }
    let mut above = value;
    for word in &mut above {
        let (next, carry) = word.overflowing_add(1);
        *word = next;
        if !carry {
            break;
        }
    }
    [below, value, above]
}

#[test]
fn full_width_reduction_matches_independent_scalar() {
    let mut cases = vec![[0; WIDE_WORDS], [u64::MAX; WIDE_WORDS]];
    // Exercise every bit and carry boundary, including the 256-bit split.
    for bit in 0..512 {
        let mut value = [0; WIDE_WORDS];
        value[bit / 64] = 1 << (bit % 64);
        cases.extend(neighbors(value));
    }
    let l: [u64; 4] =
        core::array::from_fn(|i| u64::from_le_bytes(L_BYTES[8 * i..8 * i + 8].try_into().unwrap()));
    // L*2^shift and its neighbors check canonicalization over the full input.
    for shift in 0..260 {
        let mut value = [0; WIDE_WORDS];
        for (i, word) in l.iter().enumerate() {
            value[i + shift / 64] |= word << (shift % 64);
            if shift % 64 != 0 && i + shift / 64 + 1 < WIDE_WORDS {
                value[i + shift / 64 + 1] |= word >> (64 - shift % 64);
            }
        }
        cases.extend(neighbors(value));
    }
    let mut rng = StdRng::seed_from_u64(0x5ca1_a252);
    cases.extend((0..8192).map(|_| core::array::from_fn(|_| rng.next_u64())));
    for (batch, inputs) in cases.chunks(LANES).enumerate() {
        let words = core::array::from_fn(|word| {
            core::array::from_fn(|lane| inputs[lane % inputs.len()][word])
        });
        let expected = reference_bytes(&words);
        assert_eq!(reduce(&words), reference_limbs(&expected), "batch {batch}");
        let digits = wide_words_to_radix16(&words);
        for lane in 0..LANES {
            assert_eq!(
                digits[lane],
                reference_radix16(expected[lane]),
                "batch {batch}, lane {lane} recoding"
            );
        }
    }
}

#[test]
fn radix16_carries_across_limb_and_word_boundaries_in_each_lane() {
    for start in 0..63 {
        let mut words = [[0u64; LANES]; WIDE_WORDS];
        let mut expected = [[0i8; 64]; LANES];
        for (lane, digits) in expected.iter_mut().enumerate() {
            let end = 63 - lane;
            let first = (start + lane) % end;
            // Nibble 8 starts a carry, each following 7 propagates it, and
            // zero absorbs it. The top input nibble is zero, so H < L.
            for digit in first..end {
                let nibble = if digit == first { 8 } else { 7 };
                words[digit / 16][lane] |= nibble << (4 * (digit % 16));
            }
            digits[first..end].fill(-8);
            digits[end] = 1;
        }
        assert_eq!(wide_words_to_radix16(&words), expected);
    }
}

/// ED25519_SCALAR_PATH selects the reducer (selected) or digest-to-digits (digits).
#[test]
#[ignore = "isolated eight-lane scalar reduction benchmark"]
#[allow(clippy::assertions_on_constants)]
fn profile_scalar_reduce() {
    use std::{hint::black_box, time::Instant};
    assert!(!cfg!(debug_assertions), "benchmark in release mode");
    let iterations: usize = std::env::var("ED25519_SCALAR_ITERS")
        .map(|s| s.parse().expect("ED25519_SCALAR_ITERS must be an integer"))
        .unwrap_or(5_000_000);
    assert!(iterations > 0);
    let path = std::env::var("ED25519_SCALAR_PATH").unwrap_or("selected".into());
    let mut rng = StdRng::seed_from_u64(0x5ca1_a252);
    let words = core::array::from_fn(|_| core::array::from_fn(|_| rng.next_u64()));
    fn measure<T>(
        words: &[[u64; LANES]; WIDE_WORDS],
        iterations: usize,
        run: impl Fn(&[[u64; LANES]; WIDE_WORDS]) -> T,
    ) -> f64 {
        for _ in 0..10_000 {
            black_box(run(black_box(words)));
        }
        let start = Instant::now();
        for _ in 0..iterations {
            black_box(run(black_box(words)));
        }
        start.elapsed().as_secs_f64() * 1e9 / iterations as f64
    }
    let ns = match path.as_str() {
        "selected" => measure(&words, iterations, reduce),
        "digits" => measure(&words, iterations, wide_words_to_radix16),
        _ => panic!("unknown scalar path: {path}"),
    };
    eprintln!("{ns:.2} ns/call ({path}, eight lanes, {iterations} calls, asm enabled)");
}

#[test]
fn eight_lane_reduction_and_radix16_match_vectors() {
    let fixture: serde_json::Value =
        serde_json::from_str(include_str!("../../../tests/vectors/scalar_reduction.json")).unwrap();
    let cases = fixture["cases"].as_array().unwrap();
    assert_eq!(cases.len(), LANES);

    let words: [[u64; LANES]; WIDE_WORDS] = core::array::from_fn(|word| {
        core::array::from_fn(|lane| cases[lane]["words"][word].as_u64().unwrap())
    });
    let reduced = core::array::from_fn(|lane| {
        let mut bytes = [0u8; 32];
        hex::decode_to_slice(cases[lane]["reduced"].as_str().unwrap(), &mut bytes).unwrap();
        bytes
    });
    assert_eq!(reduce(&words), reference_limbs(&reduced));
    let digits = wide_words_to_radix16(&words);
    for lane in 0..LANES {
        let expected_digits: Radix16 =
            core::array::from_fn(|digit| cases[lane]["radix16"][digit].as_i64().unwrap() as i8);

        assert_eq!(digits[lane], expected_digits, "lane {lane} recoding");
    }
}
