use super::*;
use crate::field::Fe51;
use rand::{RngCore, SeedableRng, rngs::StdRng};

fn coordinates(p: &WidePoint) -> [WideFe; 4] {
    [p.x, p.y, p.z, p.t]
}

fn assert_output(actual: &WidePoint, expected: &WidePoint, compute_t: bool) {
    for (a, b) in coordinates(actual).into_iter().zip(coordinates(expected)) {
        for (i, row) in wide_rows(a).iter().enumerate() {
            assert!(row.iter().all(|&v| v < 1 << if i == 1 { 52 } else { 51 }));
        }
        assert_eq!(a.to_bytes_lanes(), b.to_bytes_lanes());
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

fn projective(fields: [Fe51; 4]) -> CachedPoint {
    CachedPoint::from_fields(fields[1], fields[0], fields[3], fields[2])
}

fn affine(fields: [Fe51; 4]) -> AffineCachedPoint {
    AffineCachedPoint::from_fields(fields[1], fields[0], fields[2])
}

#[test]
fn cached_add_matches_integer_vectors() {
    let data: Value =
        serde_json::from_str(include_str!("../../../../tests/vectors/cached_add.json")).unwrap();
    let cases = data.as_array().unwrap();
    assert!(!cases.is_empty());
    assert_eq!(cases.len() % LANES, 0);
    for cases in cases.chunks_exact(LANES) {
        let field = |i| WideFe::from_limbs_per_lane(|lane| limbs(&cases[lane]["point"][i]));
        let input = WidePoint {
            x: field(0),
            y: field(1),
            z: field(2),
            t: field(3),
        };
        let fields: [[Fe51; 4]; LANES] = core::array::from_fn(|lane| {
            core::array::from_fn(|i| Fe51::from_limbs_unchecked(limbs(&cases[lane]["cached"][i])))
        });
        let projective = fields.map(projective);
        let affine = fields.map(affine);
        for (is_affine, compute_t) in [(false, false), (false, true), (true, true)] {
            let mut actual = Guarded::new(input);
            let mut reference = input;
            if is_affine {
                let refs = core::array::from_fn(|lane| &affine[lane]);
                actual.value.add_affine_cached_refs_assign(&refs);
                reference.add_affine_cached_refs_assign_rust(&refs);
            } else {
                let refs = core::array::from_fn(|lane| &projective[lane]);
                actual.value.add_cached_refs_assign(&refs, compute_t);
                reference.add_cached_refs_assign_rust(&refs, compute_t);
            }
            actual.check();
            assert_output(&actual.value, &reference, compute_t);
            for (i, coord) in coordinates(&actual.value).into_iter().enumerate() {
                for (lane, bytes) in coord.to_bytes_lanes().into_iter().enumerate() {
                    let expected = if i == 3 && !compute_t {
                        [0; 32]
                    } else {
                        hex_32(&cases[lane][if is_affine { "affine" } else { "projective" }][i])
                    };
                    assert_eq!(bytes, expected, "{} coordinate {i}", cases[lane]["name"]);
                }
            }
        }
    }
}

#[test]
fn cached_add_matches_rust_for_per_lane_and_aliased_selections() {
    let mut rng = StdRng::seed_from_u64(0x0cac_4eda_dd52);
    for iteration in 0..256 {
        let mut field = || core::array::from_fn(|_| rng.next_u64() & ((1 << 52) - 1));
        let inputs: [WideFe; 4] = core::array::from_fn(|_| {
            let rows: [[u64; LIMB_COUNT]; LANES] = core::array::from_fn(|_| field());
            WideFe::from_limbs_per_lane(|lane| rows[lane])
        });
        let [x, y, z, t] = inputs;
        let input = WidePoint { x, y, z, t };
        let fields: [[Fe51; 4]; LANES] =
            core::array::from_fn(|_| core::array::from_fn(|_| Fe51::from_limbs_unchecked(field())));
        let projective = fields.map(projective);
        let affine = fields.map(affine);
        let index = |lane| {
            if iteration % 7 == 0 {
                iteration % LANES
            } else {
                (3 * lane + iteration) % LANES
            }
        };
        let projective_refs = core::array::from_fn(|lane| &projective[index(lane)]);
        let affine_refs = core::array::from_fn(|lane| &affine[index(lane)]);
        for compute_t in [false, true] {
            let mut actual = Guarded::new(input);
            let mut reference = input;
            // Reuse the result to check the output/input bound transition.
            for _ in 0..2 {
                actual
                    .value
                    .add_cached_refs_assign(&projective_refs, compute_t);
                reference.add_cached_refs_assign_rust(&projective_refs, compute_t);
                assert_output(&actual.value, &reference, compute_t);
                actual.value.add_affine_cached_refs_assign(&affine_refs);
                reference.add_affine_cached_refs_assign_rust(&affine_refs);
                assert_output(&actual.value, &reference, true);
                actual.check();
            }
        }
    }
}

#[cfg(all(
    feature = "asm-cached-add",
    target_os = "linux",
    target_pointer_width = "64"
))]
mod native {
    use super::*;
    use core::ffi::{c_int, c_void};

    core::arch::global_asm!(include_str!("cached_add_abi.S"), options(raw));
    unsafe extern "C" {
        fn ed25519_simd_add_cached_ifma(
            point: *mut u8,
            cached: *const u8,
            compute_t: u64,
            affine: u64,
        );
        fn ed25519_simd_test_cached_add_abi(
            point: *mut u8,
            cached: *const u8,
            compute_t: u64,
            affine: u64,
            offset: usize,
        ) -> u64;
        fn getpagesize() -> c_int;
        fn mmap(
            address: *mut c_void,
            length: usize,
            prot: c_int,
            flags: c_int,
            fd: c_int,
            offset: i64,
        ) -> *mut c_void;
        fn mprotect(address: *mut c_void, length: usize, prot: c_int) -> c_int;
        fn munmap(address: *mut c_void, length: usize) -> c_int;
    }

    fn operands() -> (WidePoint, [WideFe; 4]) {
        let (input, mask) = decompress_points_wide(&[BASEPOINT_COMPRESSED; LANES]);
        assert_eq!(mask, u8::MAX);
        let fields = core::array::from_fn(|i| {
            WideFe::from_limbs_per_lane(|lane| {
                core::array::from_fn(|j| ((1 << 52) - 1) - (37 * i + 11 * lane + j) as u64)
            })
        });
        (input, fields)
    }

    /// Run pinned to one core in release mode with asm-pow2 enabled.
    /// ED25519_CACHED_ADD_MODE: projective, projective-no-t, or affine.
    /// ED25519_CACHED_ADD_PATH: selected (includes staging) or staged.
    /// ED25519_CACHED_ADD_ITERS controls the sampling duration.
    #[test]
    #[ignore = "isolated cached-add benchmark"]
    #[allow(clippy::assertions_on_constants)]
    fn profile_cached_add() {
        use std::{hint::black_box, time::Instant};
        assert!(cfg!(feature = "asm-pow2"), "benchmarks require asm-pow2");
        assert!(!cfg!(debug_assertions), "benchmark in release mode");
        let mode = std::env::var("ED25519_CACHED_ADD_MODE").unwrap_or("projective".into());
        let (is_affine, compute_t) = match mode.as_str() {
            "projective" => (false, true),
            "projective-no-t" => (false, false),
            "affine" => (true, true),
            _ => panic!("unknown cached-add mode: {mode}"),
        };
        let path = std::env::var("ED25519_CACHED_ADD_PATH").unwrap_or("selected".into());
        let iterations: usize = std::env::var("ED25519_CACHED_ADD_ITERS")
            .map(|n| n.parse().expect("iteration count must be an integer"))
            .unwrap_or(2_000_000);
        assert!(iterations > 0);
        let (mut point, fields) = operands();
        // These arbitrary bounded coordinates exercise the arithmetic contract;
        // curve membership is not assumed across iterations.
        let mut measure = |mut add: &mut dyn FnMut(&mut WidePoint)| {
            for _ in 0..10_000 {
                black_box(&mut add)(black_box(&mut point));
            }
            let start = Instant::now();
            for _ in 0..iterations {
                black_box(&mut add)(black_box(&mut point));
            }
            start.elapsed().as_secs_f64() * 1e9 / iterations as f64
        };
        let rows = fields.map(wide_rows);
        let scalars: [[Fe51; 4]; LANES] = core::array::from_fn(|lane| {
            core::array::from_fn(|i| {
                Fe51::from_limbs_unchecked(core::array::from_fn(|j| rows[i][j][lane]))
            })
        });
        let ns = match path.as_str() {
            "staged" => measure(&mut |p| unsafe {
                ed25519_simd_add_cached_ifma(
                    core::ptr::from_mut(p).cast(),
                    fields.as_ptr().cast(),
                    u64::from(compute_t),
                    u64::from(is_affine),
                );
            }),
            "selected" if is_affine => {
                let cached = scalars.map(affine);
                let refs = core::array::from_fn(|lane| &cached[lane]);
                measure(&mut |p| p.add_affine_cached_refs_assign(black_box(&refs)))
            }
            "selected" => {
                let cached = scalars.map(projective);
                let refs = core::array::from_fn(|lane| &cached[lane]);
                measure(&mut |p| p.add_cached_refs_assign(black_box(&refs), compute_t))
            }
            _ => panic!("unknown cached-add path: {path}"),
        };
        eprintln!("{ns:.2} ns/cached-add ({mode}, {path}, {iterations} calls, asm-pow2 enabled)");
    }

    fn expected(
        mut input: WidePoint,
        fields: [WideFe; 4],
        is_affine: bool,
        compute_t: bool,
    ) -> WidePoint {
        let rows = fields.map(wide_rows);
        let scalars: [[Fe51; 4]; LANES] = core::array::from_fn(|lane| {
            core::array::from_fn(|i| {
                Fe51::from_limbs_unchecked(core::array::from_fn(|j| rows[i][j][lane]))
            })
        });
        if is_affine {
            let cached = scalars.map(affine);
            input.add_affine_cached_refs_assign_rust(&core::array::from_fn(|lane| &cached[lane]));
            if !compute_t {
                input.t = WideFe::zero();
            }
        } else {
            let cached = scalars.map(projective);
            input.add_cached_refs_assign_rust(
                &core::array::from_fn(|lane| &cached[lane]),
                compute_t,
            );
        }
        input
    }

    #[test]
    fn cached_add_preserves_sysv_registers_and_input_bytes() {
        let (input, fields) = operands();
        for is_affine in [false, true] {
            for compute_t in [false, true] {
                let expected = expected(input, fields, is_affine, compute_t);
                for offset in [0, 16, 32, 48] {
                    let mut point = Guarded::new(input);
                    let cached = Guarded::new(fields);
                    let failure = unsafe {
                        ed25519_simd_test_cached_add_abi(
                            core::ptr::from_mut(&mut point.value).cast(),
                            cached.value.as_ptr().cast(),
                            u64::from(compute_t),
                            u64::from(is_affine),
                            offset,
                        )
                    };
                    assert_eq!(
                        failure, 0,
                        "ABI slot {failure}, affine={is_affine}, T={compute_t}, stack offset={offset}"
                    );
                    point.check();
                    cached.check();
                    assert_eq!(cached.value.map(wide_rows), fields.map(wide_rows));
                    assert_output(&point.value, &expected, compute_t);
                }
            }
        }
    }

    struct GuardPages {
        address: *mut c_void,
        length: usize,
    }
    impl Drop for GuardPages {
        fn drop(&mut self) {
            assert_eq!(unsafe { munmap(self.address, self.length) }, 0);
        }
    }

    #[test]
    fn cached_add_reads_only_supplied_fields() {
        let (input, fields) = operands();
        let page_size = usize::try_from(unsafe { getpagesize() }).unwrap();
        assert!(page_size >= 1280 && page_size % 64 == 0);
        for is_affine in [false, true] {
            // Linux x86-64: MAP_PRIVATE | MAP_ANONYMOUS, initially read/write.
            let address = unsafe { mmap(core::ptr::null_mut(), 2 * page_size, 3, 0x22, -1, 0) };
            assert_ne!(address as isize, -1);
            let pages = GuardPages {
                address,
                length: 2 * page_size,
            };
            let boundary = unsafe { address.cast::<u8>().add(page_size) };
            assert_eq!(unsafe { mprotect(boundary.cast(), page_size, 0) }, 0);
            // Affine mode must never read a fourth field, even with T enabled.
            let count = if is_affine { 3 } else { 4 };
            let cached = unsafe { boundary.sub(count * size_of::<WideFe>()).cast::<WideFe>() };
            unsafe {
                core::ptr::copy_nonoverlapping(fields.as_ptr(), cached, count);
            }
            // Also catch any store through the read-only cached input pointer.
            assert_eq!(unsafe { mprotect(address, page_size, 1) }, 0);
            for compute_t in [false, true] {
                let mut point = Guarded::new(input);
                unsafe {
                    ed25519_simd_add_cached_ifma(
                        core::ptr::from_mut(&mut point.value).cast(),
                        cached.cast(),
                        u64::from(compute_t),
                        u64::from(is_affine),
                    );
                }
                assert_output(
                    &point.value,
                    &expected(input, fields, is_affine, compute_t),
                    compute_t,
                );
                point.check();
            }
            drop(pages);
        }
    }
}
