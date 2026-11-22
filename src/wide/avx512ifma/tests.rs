use super::decode::decompress_points_wide;
use super::point::{WideFe, WidePoint};
use super::*;
use crate::edwards::{AffineCachedPoint, BASEPOINT_TABLE, CachedPoint, POINT_ENCODING_LEN};
use crate::field::LIMB_COUNT;
use curve25519::edwards::CompressedEdwardsY;
use field::{loadu, storeu};
use ladder::{PreparedChunk, mul_s_base_minus_k_public};
use serde_json::Value;

mod cached_add;
mod double4;
mod field;
mod key_table;
mod ladder;
mod ladder_step;
mod point;
mod recompress;
mod torsion;

const BASEPOINT_COMPRESSED: [u8; POINT_ENCODING_LEN] =
    curve25519::constants::ED25519_BASEPOINT_COMPRESSED.to_bytes();
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

// Test-only Fermat inversion for normalizing reference coordinates. The exponent
// p - 2 has all 255 bits set except bits 2 and 4.
fn invert(value: &WideFe) -> WideFe {
    let mut result = WideFe::one();
    for bit in (0..255).rev() {
        result = result.multiply(&result);
        if bit != 2 && bit != 4 {
            result = result.multiply(value);
        }
    }
    result
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
    assert_wide_bytes(wide.square_loose(), cases, "square", 0);
}

fn pow_p_minus_5_over_8_x2(a: &WideFe, b: &WideFe) -> (WideFe, WideFe) {
    unsafe extern "C" {
        fn ed25519_simd_pow2_ifma(out: *mut u8, a: *const u8, b: *const u8);
    }
    const _: () = assert!(size_of::<WideFe>() == 320);
    #[cfg(debug_assertions)]
    debug_assert!(
        field::limbs_are_ifma_operands(&a.limbs) && field::limbs_are_ifma_operands(&b.limbs)
    );
    let mut out = core::mem::MaybeUninit::<[WideFe; 2]>::uninit();
    // repr(C) places the five limb vectors at offsets 0,64,...,256.
    // Both inputs are readable, and the distinct output holds ten vectors.
    // Audit.pow2_contract's output_initialized guarantee covers all 640
    // bytes before return, independently of the arithmetic limb bounds.
    unsafe {
        ed25519_simd_pow2_ifma(
            out.as_mut_ptr().cast(),
            core::ptr::from_ref(a).cast(),
            core::ptr::from_ref(b).cast(),
        );
        let [x, y] = out.assume_init();
        (x, y)
    }
}

#[test]
fn paired_exponentiation_matches_vectors() {
    let vectors = vectors();
    let cases = vector_cases(&vectors, "field");
    let a = wide_from_case_inputs(cases, "a_limbs", 0);
    let b = wide_from_case_inputs(cases, "a_limbs", 3);

    let (paired_a, paired_b) = pow_p_minus_5_over_8_x2(&a, &b);
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
        black_box(pow_p_minus_5_over_8_x2(black_box(&a), black_box(&b)));
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

#[test]
fn deferred_zip215_decodes_single_and_paired_chunks() {
    use crate::field::Fe51;
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
        let (points, masks) = decode::decompress_zip215(&input.chunks, &mut both);
        for ((paired, paired_mask), bytes) in points.iter().zip(masks).zip(&input.chunks) {
            let reference = bytes.map(|b| CompressedEdwardsY(b).decompress());
            let expected = reference
                .iter()
                .enumerate()
                .fold(0u8, |mask, (j, p)| mask | (u8::from(p.is_some()) << j));
            let mut one = core::mem::MaybeUninit::uninit();
            let ([single], [single_mask]) =
                decode::decompress_zip215(core::array::from_ref(bytes), &mut one);
            assert_eq!((paired_mask, single_mask), (expected, expected));
            let encoded_y = bytes.map(|b| Fe51::from_bytes_unchecked(&b).loose_limbs());
            for point in [paired, single] {
                for (i, row) in wide_rows(point.y).iter().enumerate() {
                    assert_eq!(*row, encoded_y.map(|limbs| limbs[i]));
                }
                for field in [point.x, point.y, point.z, point.t] {
                    assert!(wide_rows(field).into_iter().flatten().all(|v| v < 1 << 52));
                }
                assert_eq!(point.z.equals_mask(&WideFe::one()), u8::MAX);
                assert_eq!(
                    point.t.equals_mask(&point.x.multiply(&point.y)) & expected,
                    expected
                );
                let normalized = point.compress();
                for (j, p) in reference.iter().enumerate() {
                    if let Some(p) = p {
                        assert_eq!(normalized[j], p.compress().to_bytes());
                    }
                }
            }
        }
    }
}

#[test]
fn public_key_table_matches_basepoint_vectors() {
    let vectors = vectors();
    let cases = vector_cases(&vectors, "basepoint_multiples");
    let public_table = decode_public_key_table(&BASEPOINT_COMPRESSED).expect("basepoint decodes");

    for case in cases {
        let scalar = case["scalar"].as_i64().expect("scalar is an integer") as i16;
        let expected = hex_32(&case["encoding"]);
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
fn embedded_basepoint_table_matches_every_signed_multiple() {
    use crate::edwards::BASEPOINT_TABLE_SIZE;
    use curve25519::{edwards::EdwardsPoint, scalar::Scalar};

    for (index, entry) in BASEPOINT_TABLE.iter().enumerate() {
        let digit = index as i16 - BASEPOINT_TABLE_SIZE as i16;
        let magnitude = Scalar::from(digit.unsigned_abs());
        let scalar = if digit < 0 { -magnitude } else { magnitude };
        let encoded = EdwardsPoint::mul_base(&scalar).compress().to_bytes();
        let (p, valid) = decompress_points_wide(&[encoded; LANES]);
        assert_eq!(valid, u8::MAX);

        let (plus, minus, t2d) = entry.coords();
        for (name, stored, expected) in [
            ("y-x", minus, p.y.subtract(&p.x)),
            ("y+x", plus, p.y.add(&p.x)),
            ("2dxy", t2d, WideFe::two_d().multiply(&p.x).multiply(&p.y)),
        ] {
            assert_eq!(
                stored.loose_limbs(),
                expected.canonical().lane0().loose_limbs(),
                "[{digit}]B {name}"
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
    let mut two = [0i8; 64];
    two[0] = 2;
    let mut one = [0i8; 64];
    one[0] = 1;
    let s_digits = [two; LANES];
    let k_digits = [one; LANES];
    let prepared = PreparedChunk {
        public_key_tables: [&table; LANES],
        s_digits: &s_digits,
        k_digits: &k_digits,
    };
    let combined = mul_s_base_minus_k_public::<true>(&BASEPOINT_TABLE, &prepared);
    // 2B - 1B = B exercises both signed-digit inputs and both tables.
    assert_eq!(combined.compress(), [BASEPOINT_COMPRESSED; LANES]);
}

#[test]
fn dalek_key_filter_preserves_eligibility_for_every_lane_mask() {
    let regular = decode_public_key_table(&BASEPOINT_COMPRESSED).unwrap();
    // y=0 represents an order-four point, so [8]A is the identity.
    let small = decode_public_key_table(&[0; 32]).unwrap();
    for mask in 0..=u8::MAX {
        let tables = core::array::from_fn(|j| {
            if mask & (1 << j) != 0 {
                &small
            } else {
                &regular
            }
        });
        for initial in [0xff_u8, 0xa5] {
            let mut valid = mask_to_lanes(initial);
            dalek::reject_small_order_keys(&tables, &mut valid);
            assert_eq!(valid, mask_to_lanes(initial & !mask));
        }
    }
}
