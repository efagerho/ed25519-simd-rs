use super::*;

fn equation_inputs() -> (WidePoint, WidePoint, WidePoint) {
    let vectors = vectors();
    let multiples = vector_cases(&vectors, "basepoint_multiples");
    let encodings = core::array::from_fn(|j| hex_32(&multiples[j]["encoding"]));
    let (r, valid) = decompress_points_wide(&encodings);
    assert_eq!(valid, u8::MAX);
    let fixture = vector_cases(&vectors, "torsion_multiples")
        .iter()
        .find(|v| v["multiple"] == 1)
        .unwrap();
    let generator = hex_32(&fixture["encoding"]);
    let (generator, valid) = decompress_points_wide(&[generator; LANES]);
    assert_eq!(valid, u8::MAX);
    let (base, valid) = decompress_points_wide(&[BASEPOINT_COMPRESSED; LANES]);
    assert_eq!(valid, u8::MAX);

    let mut torsion_multiples = [generator; LANES];
    for j in 1..LANES {
        torsion_multiples[j] = torsion_multiples[j - 1].add(&generator);
    }
    let positive = r.add(&WidePoint::from_lane0_points(&torsion_multiples));
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

#[test]
fn torsion_check_covers_all_eight_torsion_differences_and_lane_masks() {
    let (positive, negative, r) = equation_inputs();
    // Adding p to canonical limbs gives a second representation within the
    // input bound, including limb values near 2^52. Keep R affine.
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
