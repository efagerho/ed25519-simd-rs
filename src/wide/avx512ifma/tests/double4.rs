use super::*;
use rand::{Rng, RngCore, SeedableRng, rngs::StdRng};

#[test]
fn double4_matches_integer_vectors() {
    let data: Value =
        serde_json::from_str(include_str!("../../../../tests/vectors/double4.json")).unwrap();
    let cases = data.as_array().unwrap();
    assert!(!cases.is_empty());
    assert_eq!(cases.len() % LANES, 0);
    for cases in cases.chunks_exact(LANES) {
        let field = |name| WideFe::from_limbs_per_lane(|lane| limbs(&cases[lane][name]));
        let input = WidePoint {
            x: field("x"),
            y: field("y"),
            z: field("z"),
            t: WideFe::constant([u64::MAX; LIMB_COUNT]),
        };
        let mut actual = Guarded::new(input);
        actual.value.double_four_times_assign();
        actual.check();
        let reference = input.double().double().double().double();
        assert_point_output(&actual.value, &reference, true);
        for (i, coord) in coordinates(&actual.value).iter().enumerate() {
            let bytes = coord.to_bytes_lanes();
            for lane in 0..LANES {
                assert_eq!(
                    bytes[lane],
                    hex_32(&cases[lane]["output"][i]),
                    "{} coordinate {i}",
                    cases[lane]["name"]
                );
            }
        }
    }
}

#[test]
fn double4_matches_four_doublings_at_loose_bounds_and_ignores_t() {
    let mut rng = StdRng::seed_from_u64(0x0d04_b1e4);
    for _ in 0..256 {
        let mut field = || {
            let mut by_lane = [[0; LIMB_COUNT]; LANES];
            for limbs in &mut by_lane {
                limbs[0] = rng.next_u64() & ((1 << 60) - 1);
                limbs[1] = rng.gen_range(0..(1 << 52) - (limbs[0] >> 51));
                for limb in &mut limbs[2..] {
                    *limb = rng.next_u64() & ((1 << 52) - 1);
                }
            }
            WideFe::from_limbs_per_lane(|lane| by_lane[lane])
        };
        let input = WidePoint {
            x: field(),
            y: field(),
            z: field(),
            t: WideFe::zero(),
        };
        let mut actual = Guarded::new(input);
        let mut reference = input;
        for _ in 0..2 {
            // Different incoming T, including words outside any field bound,
            // must produce exactly the same output in all four coordinates.
            let mut poisoned = actual.value;
            poisoned.t = wide_from_rows(core::array::from_fn(|_| {
                core::array::from_fn(|_| rng.next_u64())
            }));
            actual.value.double_four_times_assign();
            poisoned.double_four_times_assign();
            reference = reference.double().double().double().double();
            actual.check();
            assert_point_output(&actual.value, &reference, true);
            for (a, b) in coordinates(&actual.value)
                .into_iter()
                .zip(coordinates(&poisoned))
            {
                assert_eq!(wide_rows(a), wide_rows(b), "incoming T changed the result");
            }
        }
    }
}

core::arch::global_asm!(include_str!("double4_abi.S"), options(raw));

#[test]
fn double4_preserves_sysv_registers() {
    unsafe extern "C" {
        fn ed25519_simd_test_double4_abi(point: *mut u8, stack_offset: usize) -> u64;
    }
    let (input, mask) = decompress_points_wide(&[BASEPOINT_COMPRESSED; LANES]);
    assert_eq!(mask, u8::MAX);
    let mut expected = input;
    expected = expected.double().double().double().double();
    for stack_offset in [0, 16, 32, 48] {
        let mut actual = Guarded::new(input);
        let failure = unsafe {
            ed25519_simd_test_double4_abi(
                core::ptr::from_mut(&mut actual.value).cast(),
                stack_offset,
            )
        };
        assert_eq!(
            failure, 0,
            "callee-saved register or stack slot {failure} changed with stack offset {stack_offset}"
        );
        actual.check();
        assert_point_output(&actual.value, &expected, true);
    }
}

/// Run pinned to one core in release mode.
/// Set ED25519_DOUBLE4_ITERS for longer instruction-sampling runs.
#[test]
#[ignore = "isolated four-doubling benchmark"]
#[allow(clippy::assertions_on_constants)] // Enforce configuration when the ignored benchmark runs.
fn profile_double4() {
    use std::{hint::black_box, time::Instant};
    assert!(!cfg!(debug_assertions), "benchmark in release mode");
    let iterations: usize = std::env::var("ED25519_DOUBLE4_ITERS")
        .map(|value| {
            value
                .parse()
                .expect("ED25519_DOUBLE4_ITERS must be an integer")
        })
        .unwrap_or(2_000_000);
    assert!(iterations > 0);
    let (point, mask) = decompress_points_wide(&[BASEPOINT_COMPRESSED; LANES]);
    assert_eq!(mask, u8::MAX);
    fn measure(mut point: WidePoint, iterations: usize) -> f64 {
        for _ in 0..10_000 {
            black_box(&mut point).double_four_times_assign();
        }
        let start = Instant::now();
        for _ in 0..iterations {
            black_box(&mut point).double_four_times_assign();
        }
        start.elapsed().as_secs_f64() * 1e9 / iterations as f64
    }
    let ns = measure(point, iterations);
    eprintln!("{ns:.1} ns/double4 ({iterations} calls)");
}
