use super::*;

const DALEK_BATCH: usize = 8;

fn check_dalek_candidates(
    points: &[WidePoint],
    encodings: &[EncodedPointChunk],
) -> [u8; DALEK_BATCH] {
    assert_eq!(points.len(), encodings.len());
    assert!(points.len() <= DALEK_BATCH);
    unsafe extern "C" {
        fn ed25519_simd_dalek_recompress(
            points: *const u8,
            encodings: *const u8,
            count: usize,
        ) -> u64;
    }
    // SAFETY: both slices cover count initialized chunks. WidePoint supplies
    // the alignment and these fixtures provide bounded XYZ with nonzero Z.
    unsafe {
        ed25519_simd_dalek_recompress(
            points.as_ptr().cast(),
            encodings.as_ptr().cast(),
            points.len(),
        )
        .to_le_bytes()
    }
}

#[test]
fn deferred_dalek_recompression_matches_independent_inversions() {
    let vectors = vectors();
    let multiples = vector_cases(&vectors, "basepoint_multiples");
    let mut candidates = Vec::new();
    let mut encodings = Vec::new();
    let mut expected = [0u8; DALEK_BATCH];
    for i in 0..DALEK_BATCH {
        let bytes = core::array::from_fn(|lane| {
            hex_32(&multiples[(i * LANES + lane) % multiples.len()]["encoding"])
        });
        let (point, valid) = decompress_points_wide(&bytes);
        assert_eq!(valid, u8::MAX);
        // Choose independent, nontrivial projective representatives per lane and chunk.
        let scale = WideFe::from_limbs_per_lane(|lane| [2 + (i * LANES + lane) as u64, 0, 0, 0, 0]);
        let candidate = WidePoint {
            x: point.x.multiply(&scale),
            y: point.y.multiply(&scale),
            z: scale,
            t: WideFe::zero(),
        };
        let mut supplied = candidate.compress();
        assert_eq!(supplied, bytes);
        let small_order =
            bytes.map(|b| CompressedEdwardsY(b).decompress().unwrap().is_small_order());
        for lane in 0..LANES {
            if (lane + i) % 3 == 0 {
                supplied[lane][(i * 7 + lane) % 32] ^= 0x80;
            } else if !small_order[lane] {
                expected[i] |= 1 << lane;
            }
        }
        candidates.push(candidate);
        encodings.push(supplied);
    }
    for depth in 0..=DALEK_BATCH {
        let masks = check_dalek_candidates(&candidates[..depth], &encodings[..depth]);
        assert_eq!(&masks[..depth], &expected[..depth], "depth {depth}");
        assert!(masks[depth..].iter().all(|&mask| mask == 0));
    }
}

#[test]
fn deferred_dalek_requires_exact_canonical_bytes() {
    // y = 3 is a non-small-order point; both encodings of its x sign are valid.
    let bytes: [[u8; 32]; LANES] = core::array::from_fn(|lane| {
        let mut bytes = [0; 32];
        bytes[0] = 3;
        bytes[31] = ((lane & 1) as u8) << 7;
        bytes
    });
    let (point, valid) = decompress_points_wide(&bytes);
    assert_eq!(valid, u8::MAX);
    let candidate = [point];
    assert_eq!(check_dalek_candidates(&candidate, &[bytes])[0], 0xff);
    // p+3 is the same field value with a noncanonical byte representation.
    let noncanonical = bytes.map(|r| {
        let mut alt = [0xff; 32];
        alt[0] = 0xf0;
        alt[31] = 0x7f | r[31];
        alt
    });
    assert_eq!(check_dalek_candidates(&candidate, &[noncanonical])[0], 0);
    for byte in 0..32 {
        let mut changed = bytes;
        for (bit, r) in changed.iter_mut().enumerate() {
            r[byte] ^= 1 << bit;
        }
        assert_eq!(
            check_dalek_candidates(&candidate, &[changed])[0],
            0,
            "byte {byte}"
        );
    }
}

#[test]
fn deferred_dalek_finds_a_single_matching_lane_among_loose_points() {
    // Both signs of a point with affine X = 2 exercise canonical parity near zero.
    let mut encoded = [0u8; 32];
    hex::decode_to_slice(
        "3126711e11ef574692935381d2cd2bbab5dd113c4010f91fd7c4dd7b12bf431a",
        &mut encoded,
    )
    .unwrap();
    let bytes = core::array::from_fn(|lane| {
        let mut r = encoded;
        r[31] ^= ((lane & 1) as u8) << 7;
        r
    });
    let (point, valid) = decompress_points_wide(&bytes);
    assert_eq!(valid, u8::MAX);
    assert_eq!(wide_rows(point.x.canonical())[0][0], 2);

    let candidates: [_; DALEK_BATCH] = core::array::from_fn(|i| {
        let z = WideFe::from_limbs_per_lane(|j| [2 + (i * LANES + j) as u64, 0, 0, 0, 0]);
        WidePoint {
            x: redundant(point.x.multiply(&z)),
            y: redundant(point.y.multiply(&z)),
            z: redundant(z),
            t: WideFe::zero(),
        }
    });
    let wrong_y = bytes.map(|mut r| {
        r[0] ^= 1;
        r
    });
    let mut supplied = [wrong_y; DALEK_BATCH];
    assert_eq!(
        check_dalek_candidates(&candidates, &supplied),
        [0; DALEK_BATCH]
    );
    for i in 0..DALEK_BATCH {
        supplied[i][i] = bytes[i];
        let mut expected = [0; DALEK_BATCH];
        expected[i] = 1 << i;
        assert_eq!(check_dalek_candidates(&candidates, &supplied), expected);
        supplied[i][i] = wrong_y[i];
    }
}

/// Set ED25519_DALEK_DEPTH (chunks), ED25519_DALEK_ITERS and ED25519_DALEK_INPUT (valid, wrong-y, or wrong-sign).
#[test]
#[ignore = "isolated Dalek recompression benchmark"]
fn profile_dalek_recompression() {
    use std::{hint::black_box, time::Instant};

    let depth = std::env::var("ED25519_DALEK_DEPTH")
        .map(|v| v.parse().expect("integer chunk count"))
        .unwrap_or(DALEK_BATCH);
    let iterations = std::env::var("ED25519_DALEK_ITERS")
        .map(|v| v.parse().expect("integer iteration count"))
        .unwrap_or(20_000usize);
    let input = std::env::var("ED25519_DALEK_INPUT").unwrap_or_else(|_| "valid".into());
    assert!((1..=DALEK_BATCH).contains(&depth) && iterations > 0);

    let mut point = decompress_points_wide(&[BASEPOINT_COMPRESSED; LANES]).0;
    let mut candidates = Vec::new();
    let mut encodings = Vec::new();
    for _ in 0..depth {
        point = point.double();
        let mut bytes = point.compress();
        for lane in &mut bytes {
            match input.as_str() {
                "valid" => {}
                "wrong-y" => lane[0] ^= 1,
                "wrong-sign" => lane[31] ^= 0x80,
                _ => panic!("unknown ED25519_DALEK_INPUT"),
            }
        }
        encodings.push(bytes);
        candidates.push(point);
    }

    let run = || check_dalek_candidates(black_box(&candidates), black_box(&encodings));
    let expected = if input == "valid" { 0xff } else { 0 };
    assert!(run()[..depth].iter().all(|&mask| mask == expected));
    let start = Instant::now();
    for _ in 0..iterations {
        black_box(run());
    }
    eprintln!(
        "{depth} chunks, {input}, {:.2} ns/call",
        start.elapsed().as_secs_f64() * 1e9 / iterations as f64
    );
}
