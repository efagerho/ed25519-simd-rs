use super::*;
use crate::field::Fe51;
use rand::{Rng, RngCore, SeedableRng, rngs::StdRng};

fn coordinates(point: &WidePoint) -> [WideFe; 4] {
    [point.x, point.y, point.z, point.t]
}

fn assert_output(actual: &WidePoint, expected: &WidePoint, compute_t: bool) {
    for (a, b) in coordinates(actual).into_iter().zip(coordinates(expected)) {
        assert_eq!(a.to_bytes_lanes(), b.to_bytes_lanes());
        for (i, row) in wide_rows(a).iter().enumerate() {
            assert!(row.iter().all(|&v| v < 1 << if i == 1 { 52 } else { 51 }));
        }
    }
    if !compute_t {
        assert_eq!(wide_rows(actual.t), [[0; LANES]; LIMB_COUNT]);
    }
}

#[repr(C)]
struct Guarded<T> {
    before: [u8; 64],
    value: T,
    after: [u8; 64],
}

impl<T> Guarded<T> {
    fn new(value: T) -> Self {
        Self {
            before: [0xa5; 64],
            value,
            after: [0x5a; 64],
        }
    }

    fn check(&self) {
        assert_eq!(self.before, [0xa5; 64]);
        assert_eq!(self.after, [0x5a; 64]);
    }
}

fn reference_step(
    point: &mut WidePoint,
    odd: &[&CachedPoint; LANES],
    base: &[&AffineCachedPoint; LANES],
    even: &[&CachedPoint; LANES],
    compute_t: bool,
) {
    point.double_four_times_assign_rust();
    point.add_cached_refs_assign_rust(odd, false);
    point.double_four_times_assign_rust();
    point.add_affine_cached_refs_assign_rust(base);
    point.add_cached_refs_assign_rust(even, compute_t);
}

#[test]
fn ladder_step_matches_rust_at_loose_bounds() {
    let mut rng = StdRng::seed_from_u64(0x0256_1add_e700);
    for iteration in 0..128 {
        let mut field = || {
            let rows: [[u64; LIMB_COUNT]; LANES] = core::array::from_fn(|_| {
                let mut limbs = [0; LIMB_COUNT];
                limbs[0] = rng.next_u64() & ((1 << 60) - 1);
                limbs[1] = rng.gen_range(0..(1 << 52) - (limbs[0] >> 51));
                for limb in &mut limbs[2..] {
                    *limb = rng.next_u64() & ((1 << 52) - 1);
                }
                match iteration {
                    0 => [0; LIMB_COUNT],
                    1 => [
                        (1 << 60) - 1,
                        (1 << 52) - 512,
                        (1 << 52) - 1,
                        (1 << 52) - 1,
                        (1 << 52) - 1,
                    ],
                    _ => limbs,
                }
            });
            WideFe::from_limbs_per_lane(|lane| rows[lane])
        };
        let input = WidePoint {
            x: field(),
            y: field(),
            z: field(),
            t: WideFe::constant([u64::MAX; LIMB_COUNT]),
        };
        let mut cached_field = || {
            Fe51::from_limbs_unchecked(core::array::from_fn(|_| match iteration {
                0 => 0,
                1 => (1 << 52) - 1,
                _ => rng.next_u64() & ((1 << 52) - 1),
            }))
        };
        let mut projective = || {
            core::array::from_fn(|_| {
                CachedPoint::from_fields(
                    cached_field(),
                    cached_field(),
                    cached_field(),
                    cached_field(),
                )
            })
        };
        let odd: [_; LANES] = projective();
        let even: [_; LANES] = projective();
        let base: [_; LANES] = core::array::from_fn(|_| {
            AffineCachedPoint::from_fields(cached_field(), cached_field(), cached_field())
        });
        // Include repeated references as well as distinct data in every lane.
        let index = |lane| {
            if iteration % 7 == 0 {
                iteration % LANES
            } else {
                lane
            }
        };
        let odd = core::array::from_fn(|lane| &odd[index(lane)]);
        let base = core::array::from_fn(|lane| &base[index(lane)]);
        let even = core::array::from_fn(|lane| &even[index(lane)]);
        for compute_t in [false, true] {
            let mut actual = Guarded::new(input);
            let mut expected = input;
            // Reuse the result, including a missing T, to check the handoff.
            for _ in 0..2 {
                actual
                    .value
                    .ladder_step_assign(&odd, &base, &even, compute_t);
                reference_step(&mut expected, &odd, &base, &even, compute_t);
                actual.check();
                assert_output(&actual.value, &expected, compute_t);
            }
        }
    }
}

#[test]
fn ladder_matches_single_digit_horner_schedule() {
    let base_table = BasepointTable::new();
    let (basepoint, mask) = decompress_points_wide(&[BASEPOINT_COMPRESSED; LANES]);
    assert_eq!(mask, u8::MAX);
    let tables: [_; LANES] = core::array::from_fn(|lane| {
        let mut point = basepoint;
        for _ in 0..lane {
            point = point.double();
        }
        decode_public_key_table(&point.compress()[0]).unwrap()
    });
    let tables = core::array::from_fn(|lane| &tables[lane]);
    let mut rng = StdRng::seed_from_u64(0x0002_5616);
    for case in 0..10 {
        let mut digits = || {
            core::array::from_fn(|lane| {
                core::array::from_fn(|i| match case {
                    0 => 0,
                    1 => -8,
                    2 => 7,
                    3 => {
                        if (lane + i) % 2 == 0 {
                            -8
                        } else {
                            7
                        }
                    }
                    _ => rng.gen_range(-8..=7),
                })
            })
        };
        let s_digits = digits();
        let k_digits = digits();
        let prepared = PreparedChunk {
            public_key_tables: tables,
            s_digits: &s_digits,
            k_digits: &k_digits,
        };

        // An independent 64-step schedule with one base digit per step avoids
        // sharing the pair-folding, top-digit recovery or final-T decisions.
        let mut reference = WidePoint {
            x: WideFe::zero(),
            y: WideFe::one(),
            z: WideFe::one(),
            t: WideFe::zero(),
        };
        for digit in (0..64).rev() {
            reference.double_four_times_assign_rust();
            let base = core::array::from_fn(|lane| {
                select_signed_affine_cached_ref(base_table.entries(), s_digits[lane][digit] as i16)
            });
            reference.add_affine_cached_refs_assign_rust(&base);
            let public = core::array::from_fn(|lane| {
                tables[lane].select_signed_cached_ref(-k_digits[lane][digit])
            });
            reference.add_cached_refs_assign_rust(&public, true);
        }
        let expected = reference.compress();
        let full = mul_s_base_minus_k_public::<true>(base_table.entries(), &prepared);
        let partial = mul_s_base_minus_k_public::<false>(base_table.entries(), &prepared);
        assert_eq!(full.compress(), expected, "full, case {case}");
        assert_eq!(partial.compress(), expected, "partial, case {case}");
        assert_eq!(
            full.t.multiply(&full.z).to_bytes_lanes(),
            full.x.multiply(&full.y).to_bytes_lanes()
        );
        assert_eq!(wide_rows(partial.t), [[0; LANES]; LIMB_COUNT]);
    }
}

#[cfg(all(feature = "asm", target_os = "linux", target_pointer_width = "64"))]
core::arch::global_asm!(include_str!("ladder_step_abi.S"), options(raw));

#[cfg(all(feature = "asm", target_os = "linux", target_pointer_width = "64"))]
#[test]
fn ladder_step_preserves_sysv_registers_and_staged_operands() {
    unsafe extern "C" {
        fn ed25519_simd_test_ladder_step_abi(
            point: *mut u8,
            operands: *const u8,
            compute_t: u64,
            stack_offset: usize,
        ) -> u64;
    }
    let (input, mask) = decompress_points_wide(&[BASEPOINT_COMPRESSED; LANES]);
    assert_eq!(mask, u8::MAX);
    let fields: [WideFe; 11] = core::array::from_fn(|i| {
        WideFe::from_limbs_per_lane(|lane| {
            core::array::from_fn(|j| ((1 << 52) - 1) - (37 * i + 11 * lane + j) as u64)
        })
    });
    let words = fields.map(wide_rows);
    let field =
        |i: usize, lane| Fe51::from_limbs_unchecked(core::array::from_fn(|j| words[i][j][lane]));
    let odd: [_; LANES] = core::array::from_fn(|lane| {
        CachedPoint::from_fields(
            field(1, lane),
            field(0, lane),
            field(3, lane),
            field(2, lane),
        )
    });
    let base: [_; LANES] = core::array::from_fn(|lane| {
        AffineCachedPoint::from_fields(field(5, lane), field(4, lane), field(6, lane))
    });
    let even: [_; LANES] = core::array::from_fn(|lane| {
        CachedPoint::from_fields(
            field(8, lane),
            field(7, lane),
            field(10, lane),
            field(9, lane),
        )
    });
    let operands = Guarded::new(fields);
    for compute_t in [false, true] {
        let mut expected = input;
        reference_step(
            &mut expected,
            &odd.each_ref(),
            &base.each_ref(),
            &even.each_ref(),
            compute_t,
        );
        for offset in [0, 16, 32, 48] {
            let mut actual = Guarded::new(input);
            let failure = unsafe {
                ed25519_simd_test_ladder_step_abi(
                    core::ptr::from_mut(&mut actual.value).cast(),
                    operands.value.as_ptr().cast(),
                    u64::from(compute_t),
                    offset,
                )
            };
            assert_eq!(failure, 0, "ABI slot {failure}, stack offset {offset}");
            actual.check();
            operands.check();
            assert_eq!(operands.value.map(wide_rows), words);
            assert_output(&actual.value, &expected, compute_t);
        }
    }
}

/// Run pinned to one core in release mode with asm (including pow2) enabled.
/// ED25519_LADDER_PATH: selected (staging + wrapper), staged, or separate
/// (Rust orchestration calling the same assembly arithmetic routines).
/// ED25519_LADDER_ITERS sets the duration; ED25519_LADDER_T=1 retains T.
#[cfg(all(feature = "asm", target_os = "linux", target_pointer_width = "64"))]
#[test]
#[ignore = "isolated eight-lane radix-256 ladder-step benchmark"]
#[allow(clippy::assertions_on_constants)]
fn profile_ladder_step() {
    use std::{hint::black_box, time::Instant};
    assert!(!cfg!(debug_assertions), "benchmark in release mode");
    let path = std::env::var("ED25519_LADDER_PATH").unwrap_or("selected".into());
    let iterations: usize = std::env::var("ED25519_LADDER_ITERS")
        .map(|n| n.parse().expect("iteration count must be an integer"))
        .unwrap_or(2_000_000);
    assert!(iterations > 0);
    let compute_t = match std::env::var("ED25519_LADDER_T").as_deref() {
        Ok("1") => true,
        Ok("0") | Err(_) => false,
        _ => panic!("ED25519_LADDER_T must be 0 or 1"),
    };
    let (input, mask) = decompress_points_wide(&[BASEPOINT_COMPRESSED; LANES]);
    assert_eq!(mask, u8::MAX);
    let fields: [WideFe; 11] = core::array::from_fn(|i| {
        WideFe::from_limbs_per_lane(|lane| {
            core::array::from_fn(|j| ((1 << 52) - 1) - (37 * i + 11 * lane + j) as u64)
        })
    });
    let words = fields.map(wide_rows);
    let field =
        |i: usize, lane| Fe51::from_limbs_unchecked(core::array::from_fn(|j| words[i][j][lane]));
    let odd: [_; LANES] = core::array::from_fn(|lane| {
        CachedPoint::from_fields(
            field(1, lane),
            field(0, lane),
            field(3, lane),
            field(2, lane),
        )
    });
    let base: [_; LANES] = core::array::from_fn(|lane| {
        AffineCachedPoint::from_fields(field(5, lane), field(4, lane), field(6, lane))
    });
    let even: [_; LANES] = core::array::from_fn(|lane| {
        CachedPoint::from_fields(
            field(8, lane),
            field(7, lane),
            field(10, lane),
            field(9, lane),
        )
    });
    let odd = odd.each_ref();
    let base = base.each_ref();
    let even = even.each_ref();
    fn measure(
        mut point: WidePoint,
        iterations: usize,
        mut step: impl FnMut(&mut WidePoint),
    ) -> f64 {
        for _ in 0..10_000 {
            step(black_box(&mut point));
        }
        let start = Instant::now();
        for _ in 0..iterations {
            step(black_box(&mut point));
        }
        start.elapsed().as_secs_f64() * 1e9 / iterations as f64
    }
    let ns = match path.as_str() {
        "selected" => measure(input, iterations, |p| {
            p.ladder_step_assign(
                black_box(&odd),
                black_box(&base),
                black_box(&even),
                compute_t,
            )
        }),
        "staged" => {
            unsafe extern "C" {
                fn ed25519_simd_ladder_step_ifma(
                    point: *mut u8,
                    operands: *const u8,
                    compute_t: u64,
                );
            }
            measure(input, iterations, |p| unsafe {
                ed25519_simd_ladder_step_ifma(
                    core::ptr::from_mut(p).cast(),
                    black_box(fields.as_ptr().cast()),
                    u64::from(compute_t),
                );
            })
        }
        "separate" => measure(input, iterations, |p| {
            p.double_four_times_assign();
            p.add_cached_refs_assign(black_box(&odd), false);
            p.double_four_times_assign();
            p.add_affine_cached_refs_assign(black_box(&base));
            p.add_cached_refs_assign(black_box(&even), compute_t);
        }),
        _ => panic!("unknown ladder path: {path}"),
    };
    eprintln!(
        "{ns:.2} ns/ladder-step ({path}, compute_t={compute_t}, {iterations} calls, asm enabled)"
    );
}
