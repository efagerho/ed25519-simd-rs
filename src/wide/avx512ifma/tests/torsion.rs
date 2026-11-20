use super::*;

fn torsion_multiples(vectors: &Value) -> WidePoint {
    let fixture = vector_cases(vectors, "torsion_multiples")
        .iter()
        .find(|v| v["multiple"] == 1)
        .unwrap();
    let generator = hex_32(&fixture["encoding"]);
    let (generator, valid) = decompress_points_wide(&[generator; LANES]);
    assert_eq!(valid, u8::MAX);
    let mut torsion_multiples = [generator; LANES];
    for j in 1..LANES {
        torsion_multiples[j] = torsion_multiples[j - 1].add(&generator);
    }
    WidePoint::from_lane0_points(&torsion_multiples)
}

fn equation_inputs() -> (WidePoint, WidePoint, WidePoint) {
    let vectors = vectors();
    let multiples = vector_cases(&vectors, "basepoint_multiples");
    let encodings = core::array::from_fn(|j| hex_32(&multiples[j]["encoding"]));
    let (r, valid) = decompress_points_wide(&encodings);
    assert_eq!(valid, u8::MAX);
    let (base, valid) = decompress_points_wide(&[BASEPOINT_COMPRESSED; LANES]);
    assert_eq!(valid, u8::MAX);
    let positive = r.add(&torsion_multiples(&vectors));
    (positive, positive.add(&base), r)
}

// The ladder returns projective coordinates even when P equals affine R.
fn rescale_affine(r: &WidePoint) -> WidePoint {
    let scale = WideFe::constant([37, 0, 0, 0, 0]);
    WidePoint {
        x: r.x.multiply(&scale),
        y: r.y.multiply(&scale),
        z: scale,
        t: r.t.multiply(&scale),
    }
}

#[test]
fn torsion_check_requires_all_lanes_for_early_acceptance() {
    let (_, negative, r) = equation_inputs();
    let equal = rescale_affine(&r);
    assert_eq!(equal.subtract_affine_and_check_8_torsion(&r), [true; LANES]);
    for lane in 0..LANES {
        let bad = 1u8 << lane;
        let p = WidePoint {
            x: equal.x.blend(bad, &negative.x),
            y: equal.y.blend(bad, &negative.y),
            z: equal.z.blend(bad, &negative.z),
            t: equal.t.blend(bad, &negative.t),
        };
        assert_eq!(
            p.subtract_affine_and_check_8_torsion(&r),
            mask_to_lanes(!bad)
        );
    }
}

// A second representation within the input bound, including limbs near 2^52.
fn redundant(v: WideFe) -> WideFe {
    let mut rows = wide_rows(v.canonical());
    for (j, row) in rows.iter_mut().enumerate() {
        let bias = (1u64 << 51) - if j == 0 { 19 } else { 1 };
        for limb in row {
            *limb += bias;
        }
    }
    wide_from_rows(rows)
}

#[test]
fn small_order_matches_three_doublings_for_every_mask() {
    let torsion = torsion_multiples(&vectors());
    let (base, valid) = decompress_points_wide(&[BASEPOINT_COMPRESSED; LANES]);
    assert_eq!(valid, u8::MAX);
    let ordinary = torsion.add(&base);
    let scale = WideFe::from_limbs_per_lane(|lane| [37 + lane as u64, 0, 0, 0, 0]);
    for mask in 0..=u8::MAX {
        let select = |a: WideFe, b: WideFe| a.blend(mask, &b).multiply(&scale).canonical();
        let p = WidePoint {
            x: select(ordinary.x, torsion.x),
            y: select(ordinary.y, torsion.y),
            z: select(ordinary.z, torsion.z),
            t: WideFe::zero(), // The Dalek ladder omits T.
        };
        let expected = mask_to_lanes(mask);
        assert_eq!(p.is_small_order_lanes_rust(), expected);
        assert_eq!(p.is_small_order_lanes(), expected);
        let loose = WidePoint {
            x: redundant(p.x),
            y: redundant(p.y),
            ..p
        };
        assert_eq!(loose.is_small_order_lanes(), expected);
    }
}

#[test]
fn small_order_zero_test_handles_redundant_zeros_and_neighbors() {
    let b = 1u64 << 51;
    let p = [b - 19, b - 1, b - 1, b - 1, b - 1];
    let twice_p = p.map(|digit| 2 * digit);
    let mut twice_p_minus_one = twice_p;
    twice_p_minus_one[0] -= 1;
    let inputs = [
        [0; 5],
        p,
        twice_p,
        [2 * b - 19, b - 2, b - 1, b - 1, b - 1],
        [1, 0, 0, 0, 0],
        [b - 18, b - 1, b - 1, b - 1, b - 1],
        [b - 20, b - 1, b - 1, b - 1, b - 1],
        twice_p_minus_one,
    ];
    let values = WideFe::from_limbs_per_lane(|lane| inputs[lane]);
    // With the other operand equal to one, neither +1 nor -1 is a root
    // of X^2 + Y^2. Only the four encodings of zero should set a bit.
    for (x, y) in [(values, WideFe::one()), (WideFe::one(), values)] {
        let p = WidePoint {
            x,
            y,
            z: WideFe::one(),
            t: WideFe::zero(),
        };
        assert_eq!(p.is_small_order_lanes(), mask_to_lanes(0x0f));
    }
}

#[test]
fn small_order_filter_keeps_isolated_roots_and_checks_their_neighbors() {
    use rand::{RngCore, SeedableRng, rngs::StdRng};

    let mut rng = StdRng::seed_from_u64(0x8ed2_5519);
    let max = (1u64 << 52) - 1;
    for round in 0..64 {
        // The first two choices maximize the rounding error in opposite
        // directions. The other batches vary every limb independently.
        let y = wide_from_rows(core::array::from_fn(|j| {
            core::array::from_fn(|_| match round {
                0 => [max, max, 0, 0, 0][j],
                1 => [0, 0, max, max, max][j],
                _ => rng.next_u64() & max,
            })
        }));
        let iy = y.multiply(&WideFe::sqrt_m1()).canonical();
        for root in [iy, iy.negate().canonical()] {
            // (2^252, 1) falls outside all four windows. Only the selected
            // lane can trigger the exact check.
            let mask = 1 << (round % LANES);
            let ordinary_x = WideFe::constant([0, 0, 0, 0, 1 << 48]);
            let p = WidePoint {
                x: redundant(ordinary_x.blend(mask, &root)),
                y: WideFe::one().blend(mask, &y),
                z: WideFe::one(),
                t: WideFe::zero(),
            };
            assert_eq!(p.is_small_order_lanes(), mask_to_lanes(mask));

            // Moving X by one stays within the window but fails the exact test.
            let neighbor = WidePoint {
                x: redundant(root.add(&WideFe::one())),
                y,
                ..p
            };
            assert_eq!(neighbor.is_small_order_lanes(), [false; LANES]);
        }
    }
}

#[test]
fn torsion_check_covers_all_eight_torsion_differences_and_lane_masks() {
    let (positive, negative, r) = equation_inputs();
    let r = WidePoint {
        x: redundant(r.x),
        y: redundant(r.y),
        t: redundant(r.t),
        z: r.z,
    };
    assert_eq!(r.subtract_affine_and_check_8_torsion(&r), [true; LANES]);
    for mask in 0..=u8::MAX {
        let choose = |p: WideFe, n: WideFe| redundant(n.blend(mask, &p));
        let p = WidePoint {
            x: choose(positive.x, negative.x),
            y: choose(positive.y, negative.y),
            z: choose(positive.z, negative.z),
            t: choose(positive.t, negative.t),
        };
        let expected = mask_to_lanes(mask);
        assert_eq!(p.subtract_affine_and_check_8_torsion_rust(&r), expected);
        assert_eq!(p.subtract_affine_and_check_8_torsion(&r), expected);
    }
}

/// Run pinned in release mode with `--features asm`. Select equal, torsion,
/// or unequal inputs with `ED25519_TORSION_INPUT`.
#[test]
#[ignore = "isolated eight-lane ZIP-215 equation check"]
#[allow(clippy::assertions_on_constants)]
fn profile_torsion_check() {
    use std::{hint::black_box, time::Instant};
    assert!(!cfg!(debug_assertions), "benchmark in release mode");
    let (torsion, negative, r) = equation_inputs();
    let case = std::env::var("ED25519_TORSION_INPUT").unwrap_or_else(|_| "torsion".into());
    let p = match case.as_str() {
        "equal" => rescale_affine(&r),
        "torsion" => torsion,
        "unequal" => negative,
        _ => panic!("unknown torsion input {case}"),
    };
    let path = std::env::var("ED25519_TORSION_PATH").unwrap_or_else(|_| "asm".into());
    let iters: usize = std::env::var("ED25519_TORSION_ITERS")
        .map(|n| n.parse().expect("iteration count"))
        .unwrap_or(1_000_000);
    assert!(iters > 0);
    fn measure(iters: usize, mut f: impl FnMut() -> [bool; LANES]) -> f64 {
        for _ in 0..10_000 {
            black_box(f());
        }
        let start = Instant::now();
        for _ in 0..iters {
            black_box(f());
        }
        start.elapsed().as_secs_f64() * 1e9 / iters as f64
    }
    let ns = match path.as_str() {
        "asm" => measure(iters, || {
            black_box(&p).subtract_affine_and_check_8_torsion(black_box(&r))
        }),
        "rust" => measure(iters, || {
            black_box(&p).subtract_affine_and_check_8_torsion_rust(black_box(&r))
        }),
        _ => panic!("unknown torsion check path {path}"),
    };
    eprintln!("{path}/{case}: {ns:.2} ns/eight-lane check");
}
