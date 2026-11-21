use super::decode::decompress_points_wide;
use super::field::{WideFe, loadu, storeu};
use super::ladder_step::mul_s_base_minus_k_public;
use super::point::WidePoint;
use super::*;
use crate::edwards::{
    AffineCachedPoint, BASEPOINT_COMPRESSED, BasepointTable, CachedPoint, POINT_ENCODING_LEN,
    select_signed_affine_cached_ref,
};
use crate::field::LIMB_COUNT;
use crate::wide::PreparedChunk;
use serde_json::Value;

mod cached_add;
mod double4;
mod ladder_step;
#[cfg(all(feature = "asm", target_os = "linux", target_pointer_width = "64"))]
mod torsion;

const VECTOR_JSON: &str = include_str!("../../../tests/vectors/avx512ifma.json");

fn vectors() -> Value {
    serde_json::from_str(VECTOR_JSON).expect("valid AVX-512 IFMA vectors")
}

fn vector_cases<'a>(vectors: &'a Value, name: &str) -> &'a [Value] {
    vectors[name]
        .as_array()
        .unwrap_or_else(|| panic!("{name} must be an array"))
}

fn hex_32(value: &Value) -> [u8; POINT_ENCODING_LEN] {
    let mut out = [0u8; POINT_ENCODING_LEN];
    hex::decode_to_slice(
        value.as_str().expect("hex vector must be a string"),
        &mut out,
    )
    .expect("valid 32-byte vector");
    out
}

fn limbs(value: &Value) -> [u64; LIMB_COUNT] {
    let values = value.as_array().expect("limbs must be an array");
    assert_eq!(values.len(), LIMB_COUNT);
    core::array::from_fn(|i| values[i].as_u64().expect("limb must be a u64"))
}

fn wide_from_rows(rows: [[u64; LANES]; LIMB_COUNT]) -> WideFe {
    WideFe {
        limbs: core::array::from_fn(|i| loadu(rows[i])),
    }
}

fn wide_rows(value: WideFe) -> [[u64; LANES]; LIMB_COUNT] {
    let mut rows = [[0u64; LANES]; LIMB_COUNT];
    for (limb, row) in rows.iter_mut().enumerate() {
        storeu(value.limbs[limb], row);
    }
    rows
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

fn wide_from_case_inputs(cases: &[Value], name: &str, offset: usize) -> WideFe {
    assert_eq!(cases.len(), LANES);
    let by_lane: [[u64; LIMB_COUNT]; LANES] =
        core::array::from_fn(|lane| limbs(&cases[(lane + offset) % LANES][name]));
    wide_from_rows(core::array::from_fn(|limb| {
        core::array::from_fn(|lane| by_lane[lane][limb])
    }))
}

fn assert_wide_bytes(actual: WideFe, cases: &[Value], expected_name: &str, offset: usize) {
    let actual = actual.to_bytes_lanes();
    for lane in 0..LANES {
        assert_eq!(
            actual[lane],
            hex_32(&cases[(lane + offset) % LANES][expected_name]),
            "{expected_name} lane {lane}"
        );
    }
}

fn cached_encoding(point: &CachedPoint) -> [u8; POINT_ENCODING_LEN] {
    let (y_plus_x, y_minus_x, z2, _) = point.coords();
    let y_plus_x = WideFe::from_field_refs(&[y_plus_x; LANES]);
    let y_minus_x = WideFe::from_field_refs(&[y_minus_x; LANES]);
    let point = WidePoint {
        x: y_plus_x.subtract(&y_minus_x),
        y: y_plus_x.add_loose(&y_minus_x),
        z: WideFe::from_field_refs(&[z2; LANES]),
        t: WideFe::zero(),
    };
    point.compress()[0]
}

fn affine_cached_encoding(point: &AffineCachedPoint) -> [u8; POINT_ENCODING_LEN] {
    let (y_plus_x, y_minus_x, _) = point.coords();
    let y_plus_x = WideFe::from_field_refs(&[y_plus_x; LANES]);
    let y_minus_x = WideFe::from_field_refs(&[y_minus_x; LANES]);
    let point = WidePoint {
        x: y_plus_x.subtract(&y_minus_x),
        y: y_plus_x.add_loose(&y_minus_x),
        z: WideFe::one().double(),
        t: WideFe::zero(),
    };
    point.compress()[0]
}

fn strict_square_n(x: &WideFe, n: usize) -> WideFe {
    let mut out = *x;
    for _ in 0..n {
        out = out.square();
    }
    out
}

#[test]
fn canonical_matches_vectors() {
    let vectors = vectors();
    let cases = vector_cases(&vectors, "canonical");
    assert_eq!(cases.len(), LANES);

    let by_lane: [[u64; LIMB_COUNT]; LANES] =
        core::array::from_fn(|lane| limbs(&cases[lane]["input_limbs"]));
    let wide = wide_from_rows(core::array::from_fn(|limb| {
        core::array::from_fn(|lane| by_lane[lane][limb])
    }));
    let actual = wide_rows(wide.canonical());
    let is_zero = wide.is_zero_lanes();
    let is_odd = wide.is_odd_lanes();

    for lane in 0..LANES {
        let expected = limbs(&cases[lane]["expected_limbs"]);
        let actual_lane = core::array::from_fn(|limb| actual[limb][lane]);
        assert_eq!(actual_lane, expected, "canonical lane {lane}");
        assert_eq!(
            is_zero[lane],
            expected == [0; LIMB_COUNT],
            "zero lane {lane}"
        );
        assert_eq!(is_odd[lane], expected[0] & 1 != 0, "odd lane {lane}");
    }
}

#[test]
fn wide_field_operations_match_vectors() {
    let vectors = vectors();
    let cases = vector_cases(&vectors, "field");
    let a = wide_from_case_inputs(cases, "a_limbs", 0);
    let b = wide_from_case_inputs(cases, "b_limbs", 0);
    let c = wide_from_case_inputs(cases, "c_limbs", 0);

    assert_wide_bytes(a.add(&b), cases, "add", 0);
    assert_wide_bytes(a.add_loose(&b), cases, "add", 0);
    assert_wide_bytes(a.subtract(&b), cases, "subtract", 0);
    assert_wide_bytes(a.multiply(&b), cases, "multiply", 0);
    assert_wide_bytes(a.multiply_loose(&b), cases, "multiply", 0);
    assert_wide_bytes(a.square(), cases, "square", 0);
    assert_wide_bytes(a.square_loose(), cases, "square", 0);

    let ab = a.multiply_loose(&b);
    let bc = b.multiply_loose(&c);
    let cc = c.square_loose();
    assert_wide_bytes(ab.subtract_loose(&bc), cases, "subtract_loose", 0);
    assert_wide_bytes(ab.subtract_loose_sum(&bc, &cc), cases, "subtract_sum", 0);
    assert_wide_bytes(
        ab.subtract_loose_sum_with_doubled_rhs(&bc, &cc),
        cases,
        "subtract_sum_doubled",
        0,
    );
    assert_wide_bytes(WideFe::negate_loose_sum(&bc, &cc), cases, "negate_sum", 0);
}

#[test]
fn loose_limb0_bound_matches_vectors() {
    let vectors = vectors();
    let cases = vector_cases(&vectors, "loose_bound");
    let wide = wide_from_case_inputs(cases, "input_limbs", 0);

    assert_wide_bytes(wide.subtract_loose(&wide), cases, "zero", 0);
    assert_wide_bytes(wide.subtract_loose_sum(&wide, &wide), cases, "negate", 0);
    assert_wide_bytes(
        wide.subtract_loose_sum_with_doubled_rhs(&wide, &wide),
        cases,
        "double_negate",
        0,
    );
    assert_wide_bytes(
        WideFe::negate_loose_sum(&wide, &wide),
        cases,
        "double_negate",
        0,
    );
    assert_wide_bytes(wide.square(), cases, "square", 0);
    assert_wide_bytes(wide.square_loose(), cases, "square", 0);
}

#[test]
fn square_repeat_variants_match_strict_simd_result() {
    let a = WideFe::constant(crate::field::D_LIMBS);
    let b = WideFe::constant(crate::field::SQRT_M1_LIMBS);
    macro_rules! check {
        ($n:literal) => {
            assert!(
                WideFe::square_repeat::<$n>(&a)
                    .equals_lanes(&strict_square_n(&a, $n))
                    .iter()
                    .all(|&v| v),
                "square_repeat::<{}> diverged for a",
                $n
            );
            assert!(
                WideFe::square_repeat::<$n>(&b)
                    .equals_lanes(&strict_square_n(&b, $n))
                    .iter()
                    .all(|&v| v),
                "square_repeat::<{}> diverged for b",
                $n
            );
            let (xa, xb) = WideFe::square_repeat_x2::<$n>(&a, &b);
            assert!(
                xa.equals_lanes(&strict_square_n(&a, $n)).iter().all(|&v| v),
                "square_repeat_x2::<{}> diverged for a",
                $n
            );
            assert!(
                xb.equals_lanes(&strict_square_n(&b, $n)).iter().all(|&v| v),
                "square_repeat_x2::<{}> diverged for b",
                $n
            );
        };
    }
    check!(0);
    check!(1);
    check!(2);
    check!(5);
    check!(10);
    check!(20);
    check!(50);
    check!(100);
}

#[test]
fn pow_variants_match_vectors() {
    let vectors = vectors();
    let cases = vector_cases(&vectors, "field");
    let a = wide_from_case_inputs(cases, "a_limbs", 0);
    let b = wide_from_case_inputs(cases, "a_limbs", 3);

    assert_wide_bytes(a.pow_p_minus_5_over_8(), cases, "pow_a", 0);
    assert_wide_bytes(b.pow_p_minus_5_over_8(), cases, "pow_a", 3);

    let (paired_a, paired_b) = WideFe::pow_p_minus_5_over_8_x2(&a, &b);
    assert_wide_bytes(paired_a, cases, "pow_a", 0);
    assert_wide_bytes(paired_b, cases, "pow_a", 3);
}

/// Run in release mode, pinned to one core, with `asm` enabled.
/// Set ED25519_POW2_ITERS for longer profiling runs.
#[test]
#[ignore = "isolated paired exponentiation benchmark"]
#[allow(clippy::assertions_on_constants)]
fn profile_paired_exponentiation() {
    use std::{hint::black_box, time::Instant};

    assert!(
        cfg!(all(
            feature = "asm",
            target_os = "linux",
            target_pointer_width = "64"
        )),
        "paired exponentiation benchmarks require the asm backend"
    );
    assert!(!cfg!(debug_assertions), "benchmark in release mode");
    let iterations: usize = std::env::var("ED25519_POW2_ITERS")
        .map(|value| {
            value
                .parse()
                .expect("ED25519_POW2_ITERS must be an integer")
        })
        .unwrap_or(20_000);
    assert!(iterations > 0);
    let a = wide_from_rows(core::array::from_fn(|i| {
        core::array::from_fn(|j| ((8 * i + j + 17) as u64) * 196613)
    }));
    let b = wide_from_rows(core::array::from_fn(|i| {
        core::array::from_fn(|j| ((8 * i + j + 57) as u64) * 196613)
    }));
    let run = || {
        black_box(WideFe::pow_p_minus_5_over_8_x2(
            black_box(&a),
            black_box(&b),
        ));
    };
    for _ in 0..500 {
        run();
    }
    let start = Instant::now();
    for _ in 0..iterations {
        run();
    }
    eprintln!(
        "{:.1} ns/pair ({iterations} calls, asm enabled)",
        start.elapsed().as_secs_f64() * 1e9 / iterations as f64
    );
}

#[test]
fn wide_decompression_matches_vectors() {
    let vectors = vectors();
    let cases = vector_cases(&vectors, "decompression");

    for chunk in cases.chunks(LANES) {
        let encodings =
            core::array::from_fn(|lane| hex_32(&chunk.get(lane).unwrap_or(&chunk[0])["encoding"]));
        let (point, mask) = decompress_points_wide(&encodings);
        let normalized = point.compress();

        for lane in 0..chunk.len() {
            let expected_valid = chunk[lane]["valid"].as_bool().expect("valid is a bool");
            assert_eq!(
                mask & (1 << lane) != 0,
                expected_valid,
                "{} validity",
                chunk[lane]["name"].as_str().unwrap()
            );
            if expected_valid {
                assert_eq!(
                    normalized[lane],
                    hex_32(&chunk[lane]["normalized"]),
                    "{} normalization",
                    chunk[lane]["name"].as_str().unwrap()
                );
            }
        }
    }
}

#[cfg(all(feature = "asm", target_os = "linux", target_pointer_width = "64"))]
#[test]
fn deferred_zip215_decodes_single_and_paired_chunks() {
    use rand::{RngCore, SeedableRng, rngs::StdRng};

    #[repr(C, align(64))]
    struct Unaligned {
        prefix: u8,
        chunks: [[[u8; 32]; LANES]; 2],
    }

    let vectors = vectors();
    let mut cases: Vec<_> = vector_cases(&vectors, "decompression")
        .iter()
        .map(|case| hex_32(&case["encoding"]))
        .collect();
    // Both signs of the order-two point and all noncanonical y = p..p+18.
    for low in 0xec..=0xff {
        for high in [0x7f, 0xff] {
            let mut bytes = [0xff; 32];
            bytes[0] = low;
            bytes[31] = high;
            cases.push(bytes);
        }
    }
    // The uncorrected root is p+6 after the alternate-root multiply and
    // p+14 on the primary path. Both must use canonical parity.
    for y in [
        "aa9239e819ad147f9f634c535d82d85717a872ef0ae6c71c72571510cc4ba362",
        "b1c761d02d3bc181990152fa37afcb84012d4f3b86572ad8ced5695d4f652f6b",
    ] {
        let mut bytes = [0; 32];
        hex::decode_to_slice(y, &mut bytes).unwrap();
        cases.push(bytes);
        bytes[31] |= 0x80;
        cases.push(bytes);
    }
    let mut rng = StdRng::seed_from_u64(215);
    cases.extend((0..1024).map(|_| {
        let mut bytes = [0; 32];
        rng.fill_bytes(&mut bytes);
        bytes
    }));

    for batch in cases.chunks(2 * LANES) {
        let input = Unaligned {
            prefix: 0,
            chunks: core::array::from_fn(|c| {
                core::array::from_fn(|j| batch[(c * LANES + j) % batch.len()])
            }),
        };
        let mut both = core::mem::MaybeUninit::uninit();
        let (points, masks) = decode::decompress_deferred(&input.chunks, &mut both);
        for ((paired, paired_mask), bytes) in points.iter().zip(masks).zip(&input.chunks) {
            let (reference, expected) = decompress_points_wide(bytes);
            let mut one = core::mem::MaybeUninit::uninit();
            let ([single], [single_mask]) =
                decode::decompress_deferred(core::array::from_ref(bytes), &mut one);
            assert_eq!((paired_mask, single_mask), (expected, expected));
            for point in [paired, single] {
                for (actual, wanted) in [
                    (point.x, reference.x),
                    (point.y, reference.y),
                    (point.z, reference.z),
                    (point.t, reference.t),
                ] {
                    assert!(wide_rows(actual).into_iter().flatten().all(|v| v < 1 << 52));
                    assert_eq!(actual.equals_mask(&wanted) & expected, expected);
                }
            }
        }
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
        let small_order = candidate.is_small_order_lanes_rust();
        for lane in 0..LANES {
            if (lane + i) % 3 == 0 {
                supplied[lane][(i * 7 + lane) % 32] ^= 0x80;
            } else if !small_order[lane] {
                expected[i] |= 1 << lane;
            }
        }
        candidates.push(DalekCandidate(candidate));
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
    let candidate = [DalekCandidate(point)];
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
        DalekCandidate(WidePoint {
            x: redundant(point.x.multiply(&z)),
            y: redundant(point.y.multiply(&z)),
            z: redundant(z),
            t: WideFe::zero(),
        })
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

#[test]
fn cached_tables_match_basepoint_vectors() {
    let vectors = vectors();
    let cases = vector_cases(&vectors, "basepoint_multiples");
    let public_table = decode_public_key_table(&BASEPOINT_COMPRESSED).expect("basepoint decodes");
    let base_table = BasepointTable::new();

    for case in cases {
        let scalar = case["scalar"].as_i64().expect("scalar is an integer") as i16;
        let expected = hex_32(&case["encoding"]);
        assert_eq!(
            affine_cached_encoding(select_signed_affine_cached_ref(
                base_table.entries(),
                scalar,
            )),
            expected,
            "fixed-base table digit {scalar}"
        );
        if (-8..=8).contains(&scalar) {
            assert_eq!(
                cached_encoding(public_table.select_signed_cached_ref(scalar as i8)),
                expected,
                "public-key table digit {scalar}"
            );
        }
    }
}

#[test]
fn wide_torsion_operations_match_vectors() {
    let vectors = vectors();
    let cases = vector_cases(&vectors, "torsion_multiples");
    let encoding = |multiple: u64| {
        hex_32(
            &cases
                .iter()
                .find(|case| case["multiple"].as_u64() == Some(multiple))
                .expect("torsion multiple is present")["encoding"],
        )
    };

    let (point, mask) = decompress_points_wide(&[encoding(1); LANES]);
    assert_eq!(mask, u8::MAX);
    assert_eq!(point.compress()[0], encoding(1));

    let doubled = point.double();
    assert_eq!(doubled.compress()[0], encoding(2));
    let quadrupled = doubled.double();
    assert_eq!(quadrupled.compress()[0], encoding(4));
    let multiplied_by_eight = quadrupled.double();
    assert_eq!(multiplied_by_eight.compress()[0], encoding(8));

    let (identity, identity_mask) = decompress_points_wide(&[encoding(8); LANES]);
    assert_eq!(identity_mask, u8::MAX);
    let subtract_chain = identity.subtract(&point).double().double().double();
    assert_eq!(subtract_chain.compress()[0], encoding(8));
}

#[test]
fn wide_multiscalar_matches_nontrivial_basepoint_relation() {
    let table = decode_public_key_table(&BASEPOINT_COMPRESSED).expect("basepoint decodes");
    let base_table = BasepointTable::new();
    let mut two_bytes = [0u8; 32];
    two_bytes[0] = 2;
    let two = crate::scalar::CanonicalScalar::from_canonical_bytes(two_bytes);
    let s_digits = [two.to_radix16(); LANES];
    let mut one_bytes = [0u8; 32];
    one_bytes[0] = 1;
    let one = crate::scalar::CanonicalScalar::from_canonical_bytes(one_bytes);
    let k_digits = [one.to_radix16(); LANES];
    let prepared = PreparedChunk {
        public_key_tables: [&table; LANES],
        s_digits: &s_digits,
        k_digits: &k_digits,
    };
    let combined = mul_s_base_minus_k_public::<true>(base_table.entries(), &prepared);
    // 2B - 1B = B exercises both signed-digit inputs and both tables.
    assert_eq!(combined.compress(), [BASEPOINT_COMPRESSED; LANES]);
}

/// Set ED25519_DALEK_DEPTH (chunks), ED25519_DALEK_ITERS and ED25519_DALEK_INPUT (valid, wrong-y, or wrong-sign).
#[cfg(all(feature = "asm", target_os = "linux", target_pointer_width = "64"))]
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
        candidates.push(DalekCandidate(point));
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
