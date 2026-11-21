//! SysV interface for post-hash ZIP-215 verification.
use super::LANES;
use super::decode::WideRPoint;
use super::point::WidePoint;
use crate::batch::{EncodedPointChunk, PendingLanes};
use crate::edwards::{AffineCachedPoint, BasepointTableEntries, CachedPoint, PointTable};
use crate::scalar::Radix16;
use crate::wide::HashedChunk;
use core::mem::{MaybeUninit, align_of, offset_of, size_of};

const CHUNKS: usize = 8;

#[repr(C)]
struct Inputs {
    keys: [*const CachedPoint; LANES],
    base: *const AffineCachedPoint,
    s: *const Radix16,
    digests: *const [u64; LANES],
}

impl Inputs {
    fn new(chunk: &HashedChunk<'_>, base: &BasepointTableEntries) -> Self {
        Self {
            keys: chunk.public_key_tables.map(PointTable::entries_ptr),
            base: base.as_ptr(),
            s: chunk.s_digits.as_ptr(),
            digests: chunk.digests.as_ptr(),
        }
    }
}

// Between calls, count is below CHUNKS. The occupied slots own all data
// needed by flush, including scatter indices. No cache or output pointers
// survive a call.
#[derive(Debug)]
#[repr(C)]
struct Storage {
    points: MaybeUninit<[WidePoint; CHUNKS]>,
    encodings: MaybeUninit<[EncodedPointChunk; CHUNKS]>,
    lanes: MaybeUninit<[PendingLanes; CHUNKS]>,
    count: usize,
}

impl Default for Storage {
    fn default() -> Self {
        Self {
            points: MaybeUninit::uninit(),
            encodings: MaybeUninit::uninit(),
            lanes: MaybeUninit::uninit(),
            count: 0,
        }
    }
}

#[derive(Default, Debug)]
pub(crate) struct Queue(Option<Box<Storage>>);

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
    assert!(offset_of!(Storage, points) == 0 && offset_of!(Storage, encodings) == 10240);
    assert!(offset_of!(Storage, lanes) == 12288 && offset_of!(Storage, count) == 12928);
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
    fn ed25519_simd_zip215_push(
        queue: *mut u8,
        inputs: &Inputs,
        bytes: &EncodedPointChunk,
        lanes: &PendingLanes,
        out: *mut bool,
        len: usize,
    ) -> u32;
    fn ed25519_simd_zip215_flush(queue: *mut u8, out: *mut bool, len: usize) -> u32;
}

pub(crate) fn check_decoded(
    chunk: &HashedChunk<'_>,
    base: &BasepointTableEntries,
    r: &WideRPoint,
    r_valid: u8,
    lanes: &PendingLanes,
    out: &mut [bool],
) {
    let inputs = Inputs::new(chunk, base);
    // SAFETY: the buffers in inputs and the aligned affine point remain borrowed
    // for the call. Scatter checks each active index and writes a bool byte.
    let ok = unsafe {
        ed25519_simd_zip215_decoded(
            &inputs,
            core::ptr::from_ref(&r.point).cast(),
            r_valid,
            lanes,
            out.as_mut_ptr(),
            out.len(),
        )
    };
    assert_eq!(ok, 1, "invalid ZIP-215 output positions");
}

impl Queue {
    pub(crate) fn push(
        &mut self,
        chunk: &HashedChunk<'_>,
        base: &BasepointTableEntries,
        lanes: PendingLanes,
        out: &mut [bool],
    ) {
        let queue = self.0.get_or_insert_with(Box::default);
        let inputs = Inputs::new(chunk, base);
        // SAFETY: queue is exclusive and aligned. Push initializes the next
        // candidate, encoding and metadata slot before either can be consumed.
        let ok = unsafe {
            ed25519_simd_zip215_push(
                core::ptr::from_mut(&mut **queue).cast(),
                &inputs,
                chunk.r_bytes,
                &lanes,
                out.as_mut_ptr(),
                out.len(),
            )
        };
        assert_eq!(ok, 1, "invalid ZIP-215 output positions");
    }

    pub(crate) fn flush(&mut self, out: &mut [bool]) {
        if let Some(queue) = &mut self.0 {
            // SAFETY: flush consumes only occupied slots and bounds-checks
            // their saved indices against this exclusive output slice.
            let ok = unsafe {
                ed25519_simd_zip215_flush(
                    core::ptr::from_mut(&mut **queue).cast(),
                    out.as_mut_ptr(),
                    out.len(),
                )
            };
            assert_eq!(ok, 1, "invalid ZIP-215 output positions");
        }
    }
}
