use super::decode::decompress_points_wide;
use super::field::{WideFe, loadu, storeu};
use super::multiscalar::mul_s_base_minus_k_public;
use super::point::WidePoint;
use super::*;
use crate::edwards::{
    AffineCachedPoint, BASEPOINT_COMPRESSED, BasepointTable, CachedPoint, POINT_ENCODING_LEN,
    select_signed_affine_cached_ref,
};
use crate::field::LIMB_COUNT;
use crate::wide::PreparedChunk;
use serde_json::Value;

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
fn batched_compression_matches_independent_inversions() {
    let vectors = vectors();
    let cases: Vec<&Value> = vector_cases(&vectors, "decompression")
        .iter()
        .filter(|case| case["valid"].as_bool() == Some(true))
        .take(LANES)
        .collect();
    assert_eq!(
        cases.len(),
        LANES,
        "vectors include one valid point per lane"
    );
    let encodings = core::array::from_fn(|lane| hex_32(&cases[lane]["encoding"]));
    let (point, mask) = decompress_points_wide(&encodings);
    assert_eq!(mask, u8::MAX);

    // Repeated doubling moves every candidate off affine `Z = 1` and to
    // a distinct `Z`, so the shared inversion has to be undone
    // differently for each one.
    let mut candidates = Vec::new();
    let mut current = point;
    for _ in 0..DALEK_BATCH {
        current = current.double();
        candidates.push(DalekCandidate(current));
    }

    for depth in 1..=DALEK_BATCH {
        let expected: Vec<_> = candidates[..depth]
            .iter()
            .map(|candidate| candidate.0.compress())
            .collect();
        let expected_small_order: Vec<_> = candidates[..depth]
            .iter()
            .map(|candidate| candidate.0.is_small_order_lanes())
            .collect();
        let mut actual = vec![[[0u8; POINT_ENCODING_LEN]; LANES]; depth];
        let mut small_order = vec![[false; LANES]; depth];
        compress_dalek_candidates(&candidates[..depth], &mut actual, &mut small_order);
        assert_eq!(actual, expected, "batch of {depth} diverged");
        assert_eq!(small_order, expected_small_order);
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
