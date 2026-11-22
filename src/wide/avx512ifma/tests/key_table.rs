use super::*;
use crate::edwards::PointTable;
use core::mem::MaybeUninit;

fn cached_fields(tables: &[PointTable; LANES], digit: i8) -> [[&crate::field::Fe51; LANES]; 4] {
    let coords = tables
        .each_ref()
        .map(|table| table.select_signed_cached_ref(digit).coords());
    [
        coords.map(|c| c.0),
        coords.map(|c| c.1),
        coords.map(|c| c.2),
        coords.map(|c| c.3),
    ]
}

#[test]
fn key_tables_match_every_signed_multiple_in_both_output_modes() {
    use curve25519::{constants::EIGHT_TORSION, edwards::EdwardsPoint, scalar::Scalar};

    // Exercise ordinary, small-order and mixed-order points in distinct lanes.
    let keys: [EdwardsPoint; LANES] = core::array::from_fn(|lane| match lane {
        0..=2 => EIGHT_TORSION[lane],
        3 => EdwardsPoint::mul_base(&Scalar::from(17u64)),
        _ => EdwardsPoint::mul_base(&Scalar::from(lane as u64)) + EIGHT_TORSION[lane],
    });
    let mut encoded = keys.map(|p| p.compress().to_bytes());
    // The same identity encoded with y=p+1 and a set X sign is valid in ZIP-215.
    encoded[0] = [0xff; 32];
    encoded[0][0] = 0xee;
    let mut out = MaybeUninit::uninit();
    let (mut point, valid) = decompress_points_wide(&encoded);
    assert_eq!(valid, u8::MAX);
    let tables = decode::build_key_tables(&mut point, &mut out);
    let singles = encoded.map(|bytes| decode_public_key_table(&bytes).unwrap());

    for digit in -8i8..=8 {
        let expected = keys.map(|p| {
            let q = p * Scalar::from(digit.unsigned_abs() as u64);
            (if digit < 0 { -q } else { q }).compress().to_bytes()
        });
        let (affine, valid) = decompress_points_wide(&expected);
        assert_eq!(valid, u8::MAX);
        let all = cached_fields(tables, digit);
        let single = cached_fields(&singles, digit);
        for (batch_field, single_field) in all.iter().zip(single) {
            for (a, b) in batch_field.iter().zip(single_field) {
                assert_eq!(a.loose_limbs(), b.loose_limbs());
                assert!(a.loose_limbs().into_iter().all(|limb| limb < 1 << 52));
            }
        }
        let [plus, minus, z2, t2d] = all.map(|field| WideFe::from_field_refs(&field));
        assert_eq!(z2.is_zero_mask(), 0, "zero denominator for digit {digit}");
        for (stored, scaled) in [
            (plus, affine.y.add(&affine.x)),
            (minus, affine.y.subtract(&affine.x)),
            (t2d, WideFe::two_d().multiply(&affine.t)),
        ] {
            assert_eq!(
                stored.double().equals_mask(&z2.multiply(&scaled)),
                u8::MAX,
                "digit {digit}"
            );
        }
    }
}

#[test]
fn key_table_writes_exactly_the_requested_tables() {
    const WORDS: usize = size_of::<PointTable>() / size_of::<u64>();
    fn run<const N: usize>(mut point: WidePoint, fill: u64) -> Vec<u64> {
        // Leave a whole table before the destination and space for all eight
        // lanes after it, even when requesting just lane zero.
        let mut words = vec![fill; (LANES + 2) * WORDS];
        // SAFETY: the middle region is u64-aligned, disjoint from point,
        // and has space for N consecutive 2720-byte tables.
        let dest = unsafe {
            &mut *words
                .as_mut_ptr()
                .add(WORDS)
                .cast::<MaybeUninit<[PointTable; N]>>()
        };
        decode::build_key_tables(&mut point, dest);
        let end = (N + 1) * WORDS;
        assert!(
            words[..WORDS]
                .iter()
                .chain(&words[end..])
                .all(|w| *w == fill)
        );
        words[WORDS..end].to_vec()
    }

    let mut encoded = [BASEPOINT_COMPRESSED; LANES];
    encoded[0] = [2; 32]; // a rejected square root still produces initialized coordinates
    let (point, mask) = decompress_points_wide(&encoded);
    assert_eq!(mask, 0xfe);
    let batch = run::<LANES>(point, u64::MAX);
    assert_eq!(batch, run::<LANES>(point, 0));
    assert!(batch.iter().all(|w| *w < 1 << 52));
    assert_eq!(run::<1>(point, u64::MAX), &batch[..WORDS]);
    assert_eq!(run::<1>(point, 0), &batch[..WORDS]);
}

#[test]
#[ignore = "isolated public-key table benchmark"]
fn profile_key_tables() {
    use std::{hint::black_box, time::Instant};
    assert!(!cfg!(debug_assertions), "benchmark in release mode");
    let iterations: usize = std::env::var("ED25519_KEY_TABLE_ITERS")
        .map(|s| s.parse().expect("iteration count must be an integer"))
        .unwrap_or(500_000);
    assert!(iterations > 0);
    let (input, valid) = decompress_points_wide(&[BASEPOINT_COMPRESSED; LANES]);
    assert_eq!(valid, u8::MAX);

    fn measure<const N: usize>(input: WidePoint, iterations: usize) {
        let mut out = MaybeUninit::uninit();
        let mut run = || {
            let mut point = *black_box(&input);
            black_box(decode::build_key_tables::<N>(&mut point, &mut out));
        };
        for _ in 0..1000 {
            run();
        }
        let start = Instant::now();
        for _ in 0..iterations {
            run();
        }
        eprintln!(
            "{N} lanes: {:.1} ns/call",
            start.elapsed().as_secs_f64() * 1e9 / iterations as f64
        );
    }
    match std::env::var("ED25519_KEY_TABLE_LANES").as_deref() {
        Ok("1") => measure::<1>(input, iterations),
        Ok("8") | Err(_) => measure::<LANES>(input, iterations),
        _ => panic!("lane count must be 1 or 8"),
    }
}
