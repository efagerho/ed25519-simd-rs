use super::LANES;
use super::decode::cold_decompress_points_wide;
use super::field::WideFe;
use super::point::WidePoint;
use crate::edwards::{
    AffineCachedPoint, BASEPOINT_COMPRESSED, BASEPOINT_TABLE_SIZE, BasepointTableEntries,
    CachedPoint, PointTable,
};
use crate::field::Fe51;

/// Construct the affine fixed-base table as 17 vectors whose lanes hold
/// consecutive multiples. Montgomery batch inversion across those vectors
/// normalizes all 136 points with one eight-lane inversion.
pub(crate) fn build_basepoint_table_entries() -> Box<BasepointTableEntries> {
    let points = build_projective_basepoint_blocks();
    let inverse_z = batch_invert_basepoint_zs(&points);
    affine_basepoint_entries(&points, &inverse_z)
}

#[inline(never)]
fn build_projective_basepoint_blocks() -> Vec<WidePoint> {
    const BLOCKS: usize = BASEPOINT_TABLE_SIZE / LANES;
    const {
        assert!(BASEPOINT_TABLE_SIZE.is_multiple_of(LANES));
    }

    let (basepoint, mask) = cold_decompress_points_wide(&[BASEPOINT_COMPRESSED; LANES]);
    assert_eq!(mask, u8::MAX, "the standard basepoint must decompress");

    let (mut block, p8) = first_basepoint_block(basepoint);
    let mut points = Vec::with_capacity(BLOCKS);
    for i in 0..BLOCKS {
        points.push(block);
        if i + 1 < BLOCKS {
            block = block.cold_add(&p8);
        }
    }
    points
}

/// Build duplicated vectors B..8B, then transpose lane zero from each
/// into one vector `[B, 2B, ..., 8B]`. Keeping this stage out of the caller
/// bounds debug-build stack use despite the large SIMD point type.
#[inline(never)]
fn first_basepoint_block(basepoint: WidePoint) -> (WidePoint, WidePoint) {
    let p2 = basepoint.cold_double_from_affine();
    let p3 = p2.add_affine_rhs(&basepoint);
    let p4 = p2.double();
    let p5 = p4.add_affine_rhs(&basepoint);
    let p6 = p3.double();
    let p7 = p4.cold_add(&p3);
    let p8 = p4.double();
    (
        WidePoint::from_lane0_points(&[basepoint, p2, p3, p4, p5, p6, p7, p8]),
        p8,
    )
}

#[inline(never)]
fn batch_invert_basepoint_zs(points: &[WidePoint]) -> Vec<WideFe> {
    if points.is_empty() {
        return Vec::new();
    }

    let mut inverse_z = Vec::with_capacity(points.len());
    let mut product = points[0].z;
    inverse_z.push(product);
    for point in &points[1..] {
        product = product.multiply(&point.z);
        inverse_z.push(product);
    }
    let mut inverse_accumulator = product.cold_invert();
    for i in (1..points.len()).rev() {
        inverse_z[i] = inverse_z[i - 1].multiply(&inverse_accumulator);
        inverse_accumulator = inverse_accumulator.multiply(&points[i].z);
    }
    inverse_z[0] = inverse_accumulator;
    inverse_z
}

#[inline(never)]
fn affine_basepoint_entries(
    points: &[WidePoint],
    inverse_z: &[WideFe],
) -> Box<BasepointTableEntries> {
    let two_d = WideFe::two_d();
    let mut positive = Vec::with_capacity(BASEPOINT_TABLE_SIZE);
    let mut negative = Vec::with_capacity(BASEPOINT_TABLE_SIZE);
    for (point, zinv) in points.iter().zip(inverse_z.iter()) {
        let x = point.x.multiply(zinv);
        let y = point.y.multiply(zinv);
        let y_plus_x = y.add(&x).to_fields_loose();
        let y_minus_x = y.subtract(&x).to_fields_loose();
        let t2d = x.multiply(&y).multiply(&two_d);
        let positive_t2d = t2d.to_fields_loose();
        let negative_t2d = t2d.negate().to_fields_loose();

        for lane in 0..LANES {
            positive.push(AffineCachedPoint::from_fields(
                y_plus_x[lane],
                y_minus_x[lane],
                positive_t2d[lane],
            ));
            negative.push(AffineCachedPoint::from_fields(
                y_minus_x[lane],
                y_plus_x[lane],
                negative_t2d[lane],
            ));
        }
    }

    // Signed layout: -136B..-B, identity, B..136B.
    let mut entries = Vec::with_capacity(2 * BASEPOINT_TABLE_SIZE + 1);
    entries.extend(negative.into_iter().rev());
    entries.push(AffineCachedPoint::identity());
    entries.extend(positive);
    entries
        .into_boxed_slice()
        .try_into()
        .unwrap_or_else(|_| unreachable!("basepoint table length is fixed"))
}

/// Build the per-lane radix-16 cached tables from an already-decompressed
/// SIMD point.
/// Every slot is filled, including lanes whose decode failed; the caller
/// discards those by mask.
/// Walk `P..8P` as a depth-4 tree, handing each multiple to `write` as soon
/// as it exists so no array of eight points is ever live.
///
/// `COLD` selects the initialization-only arithmetic, whose out-of-line
/// copies keep setup call sites from perturbing the hot builder's inlining.
#[inline(always)]
fn for_each_table_multiple<const COLD: bool>(
    p: WidePoint,
    mut write: impl FnMut(usize, &WidePoint),
) {
    write(1, &p);

    let p2 = if COLD {
        p.cold_double_from_affine()
    } else {
        p.double_from_affine()
    };
    write(2, &p2);

    let p3 = p2.add_affine_rhs(&p);
    write(3, &p3);

    let p4 = p2.double();
    write(4, &p4);

    write(5, &p4.add_affine_rhs(&p));
    write(6, &p3.double());
    write(7, &if COLD { p4.cold_add(&p3) } else { p4.add(&p3) });
    write(8, &p4.double());
}

pub(super) fn build_tables_from_point(p: WidePoint, tables: &mut [Option<PointTable>; LANES]) {
    for table in tables.iter_mut() {
        // SAFETY: `for_each_table_multiple` fills positive and negative
        // 1..=8 before this function returns or any table can be selected.
        *table = Some(unsafe { PointTable::decode_destination() });
    }
    for_each_table_multiple::<false>(p, |multiple, point| {
        write_cached_multiple(multiple, point, tables)
    });
}

pub(super) fn build_lane0_table_from_point(p: WidePoint) -> PointTable {
    // SAFETY: `for_each_table_multiple` writes both signs of every
    // multiple in 1..=8 before the completed table is returned.
    let mut table = unsafe { PointTable::decode_destination() };
    for_each_table_multiple::<true>(p, |multiple, point| {
        write_cached_multiple_lane0(multiple, point, &mut table)
    });
    table
}

fn write_cached_multiple_lane0(multiple: usize, point: &WidePoint, table: &mut PointTable) {
    let y_plus_x = point.y.add(&point.x).lane0();
    let y_minus_x = point.y.subtract(&point.x).lane0();
    let z2 = point.z.double().lane0();
    let t2d = point.t.multiply(&WideFe::two_d());
    let positive = CachedPoint::from_fields(y_plus_x, y_minus_x, z2, t2d.lane0());
    let negative = CachedPoint::from_fields(y_minus_x, y_plus_x, z2, t2d.negate().lane0());
    table.set_multiple(multiple, positive, negative);
}

#[inline(never)]
fn write_cached_multiple(
    multiple: usize,
    point: &WidePoint,
    tables: &mut [Option<PointTable>; LANES],
) {
    let two_d = WideFe::two_d();
    type LaneFields = [Fe51; LANES];
    let fields: (LaneFields, LaneFields, LaneFields, LaneFields, LaneFields) = {
        let ypx = point.y.add(&point.x);
        let ymx = point.y.subtract(&point.x);
        let z2 = point.z.double();
        let t2d = point.t.multiply(&two_d);
        let neg_t2d = t2d.negate();
        (
            ypx.to_fields_loose(),
            ymx.to_fields_loose(),
            z2.to_fields_loose(),
            t2d.to_fields_loose(),
            neg_t2d.to_fields_loose(),
        )
    };

    let (ypx, ymx, z2, t2d, neg_t2d) = fields;
    for lane in 0..LANES {
        let positive = CachedPoint::from_fields(ypx[lane], ymx[lane], z2[lane], t2d[lane]);
        let negative = CachedPoint::from_fields(ymx[lane], ypx[lane], z2[lane], neg_t2d[lane]);
        tables[lane]
            .as_mut()
            .expect("table destinations were initialized")
            .set_multiple(multiple, positive, negative);
    }
}
