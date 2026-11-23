//! SysV inputs and scatter metadata for both policies.
use super::LANES;
use super::point::WidePoint;
use crate::batch::{EncodedPointChunk, PendingLanes};
use crate::edwards::{BasepointTableEntries, PointTable};
use crate::scalar::Radix16;
use core::mem::{align_of, offset_of, size_of};

#[repr(C)]
struct Inputs<'a> {
    // PointTable is transparent over its entries. Assembly indexes from entry zero.
    keys: [&'a PointTable; LANES],
    base: &'static BasepointTableEntries,
    s: &'a [Radix16; LANES],
    digests: &'a [[u64; LANES]; 8],
}

const _: () = {
    assert!(LANES == 8 && size_of::<Radix16>() == 64 && size_of::<EncodedPointChunk>() == 256);
    assert!(offset_of!(Inputs, keys) == 0 && offset_of!(Inputs, base) == 64);
    assert!(offset_of!(Inputs, s) == 72 && offset_of!(Inputs, digests) == 80);
    assert!(size_of::<Inputs>() == 88);
    assert!(size_of::<PendingLanes>() == 80 && offset_of!(PendingLanes, valid) == 0);
    assert!(
        offset_of!(PendingLanes, output_indices) == 8
            && offset_of!(PendingLanes, active_lane_count) == 72
    );
    assert!(align_of::<WidePoint>() == 64 && size_of::<WidePoint>() == 1280);
};
