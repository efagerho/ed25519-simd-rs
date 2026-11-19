use super::*;
use rand::{Rng, RngCore, SeedableRng, rngs::StdRng};

fn coordinates(point: &WidePoint) -> [WideFe; 4] {
    [point.x, point.y, point.z, point.t]
}

fn assert_output(actual: &WidePoint, expected: &WidePoint) {
    for (i, (actual, expected)) in coordinates(actual)
        .into_iter()
        .zip(coordinates(expected))
        .enumerate()
    {
        assert_eq!(
            actual.to_bytes_lanes(),
            expected.to_bytes_lanes(),
            "coordinate {i}"
        );
        for (limb, row) in wide_rows(actual).iter().enumerate() {
            let bound = 1 << if limb == 1 { 52 } else { 51 };
            assert!(
                row.iter().all(|&x| x < bound),
                "coordinate {i}, limb {limb}"
            );
        }
    }
}

#[repr(C)]
struct GuardedPoint {
    before: [u8; 64],
    point: WidePoint,
    after: [u8; 64],
}

impl GuardedPoint {
    fn new(point: WidePoint) -> Self {
        Self {
            before: [0xa5; 64],
            point,
            after: [0x5a; 64],
        }
    }

    fn check_guards(&self) {
        assert_eq!(self.before, [0xa5; 64]);
        assert_eq!(self.after, [0x5a; 64]);
    }
}

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
        let mut actual = GuardedPoint::new(input);
        actual.point.double_four_times_assign();
        actual.check_guards();
        let mut reference = input;
        reference.double_four_times_assign_rust();
        assert_output(&actual.point, &reference);
        for (i, coord) in coordinates(&actual.point).iter().enumerate() {
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
fn double4_matches_rust_at_loose_bounds_and_ignores_t() {
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
        let mut actual = GuardedPoint::new(input);
        let mut reference = input;
        for _ in 0..2 {
            // Different incoming T, including words outside any field bound,
            // must produce exactly the same output in all four coordinates.
            let mut poisoned = actual.point;
            poisoned.t = wide_from_rows(core::array::from_fn(|_| {
                core::array::from_fn(|_| rng.next_u64())
            }));
            actual.point.double_four_times_assign();
            poisoned.double_four_times_assign();
            reference.double_four_times_assign_rust();
            actual.check_guards();
            assert_output(&actual.point, &reference);
            for (a, b) in coordinates(&actual.point)
                .into_iter()
                .zip(coordinates(&poisoned))
            {
                assert_eq!(wide_rows(a), wide_rows(b), "incoming T changed the result");
            }
        }
    }
}

#[cfg(all(
    feature = "asm-double4",
    target_os = "linux",
    target_pointer_width = "64"
))]
core::arch::global_asm!(include_str!("double4_abi.S"), options(raw));

#[cfg(all(
    feature = "asm-double4",
    target_os = "linux",
    target_pointer_width = "64"
))]
#[test]
fn double4_preserves_sysv_registers() {
    unsafe extern "C" {
        fn ed25519_simd_test_double4_abi(point: *mut u8, stack_offset: usize) -> u64;
    }
    let (input, mask) = decompress_points_wide(&[BASEPOINT_COMPRESSED; LANES]);
    assert_eq!(mask, u8::MAX);
    let mut expected = input;
    expected.double_four_times_assign_rust();
    for stack_offset in [0, 16, 32, 48] {
        let mut actual = GuardedPoint::new(input);
        let failure = unsafe {
            ed25519_simd_test_double4_abi(
                core::ptr::from_mut(&mut actual.point).cast(),
                stack_offset,
            )
        };
        assert_eq!(
            failure, 0,
            "callee-saved register or stack slot {failure} changed with stack offset {stack_offset}"
        );
        actual.check_guards();
        assert_output(&actual.point, &expected);
    }
}

/// Run pinned to one core, in release mode, always with `asm-pow2` enabled.
/// Add `asm-double4` to measure assembly, omit it to measure Rust doubling.
/// Set ED25519_DOUBLE4_ITERS for longer instruction-sampling runs.
#[test]
#[ignore = "isolated four-doubling benchmark"]
#[allow(clippy::assertions_on_constants)] // Enforce configuration when the ignored benchmark runs.
fn profile_double4() {
    use std::{hint::black_box, time::Instant};
    assert!(
        cfg!(all(
            feature = "asm-pow2",
            target_os = "linux",
            target_pointer_width = "64"
        )),
        "double4 benchmarks require the asm-pow2 backend"
    );
    assert!(!cfg!(debug_assertions), "benchmark in release mode");
    let iterations: usize = std::env::var("ED25519_DOUBLE4_ITERS")
        .map(|value| {
            value
                .parse()
                .expect("ED25519_DOUBLE4_ITERS must be an integer")
        })
        .unwrap_or(2_000_000);
    assert!(iterations > 0);
    let (mut point, mask) = decompress_points_wide(&[BASEPOINT_COMPRESSED; LANES]);
    assert_eq!(mask, u8::MAX);
    for _ in 0..10_000 {
        black_box(&mut point).double_four_times_assign();
    }
    let start = Instant::now();
    for _ in 0..iterations {
        black_box(&mut point).double_four_times_assign();
    }
    eprintln!(
        "{:.1} ns/double4 ({iterations} calls, asm-pow2 enabled)",
        start.elapsed().as_secs_f64() * 1e9 / iterations as f64
    );
}
