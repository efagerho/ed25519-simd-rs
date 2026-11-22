use super::LANES;
use super::field::WideFe;
use super::point::WidePoint;
use crate::edwards::{CachedPoint, PointTable};
use crate::field::Fe51;

/// Build the per-lane radix-16 cached tables from an already-decompressed
/// SIMD point.
/// Every slot is filled, including lanes whose decode failed; the caller
/// discards those by mask.
/// Walk `P..8P` as a depth-4 tree, handing each multiple to `write` as soon
/// as it exists so no array of eight points is ever live.
#[inline(always)]
fn for_each_table_multiple(p: WidePoint, mut write: impl FnMut(usize, &WidePoint)) {
    write(1, &p);

    let p2 = p.double_from_affine();
    write(2, &p2);

    let p3 = p2.add_affine_rhs(&p);
    write(3, &p3);

    let p4 = p2.double();
    write(4, &p4);

    write(5, &p4.add_affine_rhs(&p));
    write(6, &p3.double());
    write(7, &p4.add(&p3));
    write(8, &p4.double());
}

pub(super) fn build_tables_from_point(p: WidePoint, tables: &mut [Option<PointTable>; LANES]) {
    for table in tables.iter_mut() {
        // SAFETY: `for_each_table_multiple` fills positive and negative
        // 1..=8 before this function returns or any table can be selected.
        *table = Some(unsafe { PointTable::decode_destination() });
    }
    for_each_table_multiple(p, |multiple, point| {
        write_cached_multiple(multiple, point, tables)
    });
}

pub(super) fn build_lane0_table_from_point(p: WidePoint) -> PointTable {
    // SAFETY: `for_each_table_multiple` writes both signs of every
    // multiple in 1..=8 before the completed table is returned.
    let mut table = unsafe { PointTable::decode_destination() };
    for_each_table_multiple(p, |multiple, point| {
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
    /// One transposed cached coordinate, with one scalar field per SIMD lane.
    /// Eight scalar `Y+X` values collect here before becoming one
    /// `WideFe` used by the next parallel point addition.
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
