//! SysV inputs and scatter metadata for both policies.
use super::LANES;
use super::point::WidePoint;
use super::prepare::WideRPoint;
use crate::batch::{EncodedPointChunk, PendingLanes};
use crate::edwards::{AffineCachedPoint, BASEPOINT_TABLE, CachedPoint, PointTable};
use crate::scalar::Radix16;
use crate::wide::HashedChunk;
use crate::{VerificationPolicy, VerifyPolicy};
use core::mem::{align_of, offset_of, size_of};

#[repr(C)]
struct Inputs {
    keys: [*const CachedPoint; LANES],
    base: *const AffineCachedPoint,
    s: *const Radix16,
    digests: *const [u64; LANES],
}

impl Inputs {
    fn new(chunk: &HashedChunk<'_>) -> Self {
        Self {
            keys: chunk.public_key_tables.map(PointTable::entries_ptr),
            base: BASEPOINT_TABLE.as_ptr(),
            s: chunk.s_digits.as_ptr(),
            digests: chunk.digests.as_ptr(),
        }
    }
}

const _: () = {
    assert!(LANES == 8 && size_of::<Radix16>() == 64 && size_of::<EncodedPointChunk>() == 256);
    assert!(offset_of!(Inputs, keys) == 0 && offset_of!(Inputs, base) == 64);
    assert!(offset_of!(Inputs, s) == 72 && offset_of!(Inputs, digests) == 80);
    assert!(size_of::<PendingLanes>() == 80 && offset_of!(PendingLanes, valid) == 0);
    assert!(
        offset_of!(PendingLanes, output_indices) == 8
            && offset_of!(PendingLanes, active_lane_count) == 72
    );
    assert!(align_of::<WidePoint>() == 64 && size_of::<WidePoint>() == 1280);
};

unsafe extern "C" {
    fn ed25519_simd_zip215_decoded(
        inputs: &Inputs,
        r: *const u8,
        r_valid: u8,
        lanes: &PendingLanes,
        out: *mut bool,
        len: usize,
    ) -> u32;
    fn ed25519_simd_dalek_decoded(
        inputs: &Inputs,
        r: *const u8,
        r_valid: u8,
        lanes: &PendingLanes,
        out: *mut bool,
        len: usize,
    ) -> u32;
}

pub(crate) fn check_decoded<P: VerificationPolicy>(
    chunk: &HashedChunk<'_>,
    r: &WideRPoint,
    r_valid: u8,
    lanes: &PendingLanes,
    out: &mut [bool],
) {
    let inputs = Inputs::new(chunk);
    // SAFETY: the buffers in inputs and the aligned affine point remain borrowed
    // for the call. Scatter checks each active index and writes a bool byte.
    let ok = unsafe {
        let check = if P::POLICY == VerifyPolicy::Dalek {
            ed25519_simd_dalek_decoded
        } else {
            ed25519_simd_zip215_decoded
        };
        check(
            &inputs,
            core::ptr::from_ref(&r.point).cast(),
            r_valid,
            lanes,
            out.as_mut_ptr(),
            out.len(),
        )
    };
    assert_eq!(ok, 1, "invalid verification output positions");
}
