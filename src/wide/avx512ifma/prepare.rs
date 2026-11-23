use super::LANES;
use super::point::WidePoint;
use crate::batch::EncodedPointChunk;
use crate::edwards::{IDENTITY_TABLE, PointTable};
use crate::input::{PUBLIC_KEY_LEN, SIGNATURE_LEN, VerifyInput};
use crate::scalar::Radix16;
use crate::{VerificationPolicy, VerifyPolicy};
use core::mem::{MaybeUninit, align_of, offset_of, size_of};

core::arch::global_asm!(include_str!("prepare_chunk.S"), options(raw));

#[repr(C)]
struct ChunkInputs<'a> {
    keys: [&'a [u8; PUBLIC_KEY_LEN]; LANES],
    signatures: [&'a [u8; SIGNATURE_LEN]; LANES],
}

/// Reused for one eight-lane chunk. The decoder writes A and R together.
/// The table builder uses A as its running multiple, leaving R for scoring.
#[repr(C)]
pub(crate) struct ChunkScratch {
    pub(crate) public_keys: EncodedPointChunk,
    pub(crate) r_bytes: EncodedPointChunk,
    pub(super) s_digits: [Radix16; LANES],
    key_work: WidePoint,
    /// Decoded R retains the original Y limbs for strict scoring.
    pub(super) r: WidePoint,
    tables: [PointTable; LANES],
}

/// Each pointer borrows either a table in this chunk's scratch or the identity.
#[repr(C)]
pub(crate) struct PreparedLanes<'a> {
    pub(super) tables: [&'a PointTable; LANES],
    pub(crate) valid: [bool; LANES],
    pub(super) r_valid: u8,
}

// Offsets and strides consumed by prepare_chunk.S.
const _: () = {
    assert!(LANES == 8 && PUBLIC_KEY_LEN == 32 && SIGNATURE_LEN == 64);
    assert!(size_of::<ChunkInputs>() == 128 && offset_of!(ChunkInputs, signatures) == 64);
    assert!(align_of::<ChunkScratch>() == 64);
    assert!(offset_of!(ChunkScratch, public_keys) == 0 && offset_of!(ChunkScratch, r_bytes) == 256);
    assert!(
        offset_of!(ChunkScratch, s_digits) == 512 && offset_of!(ChunkScratch, key_work) == 1024
    );
    assert!(offset_of!(ChunkScratch, r) == 2304 && offset_of!(ChunkScratch, tables) == 3584);
    assert!(size_of::<PointTable>() == 2720 && size_of::<ChunkScratch>() == 25344);
    assert!(offset_of!(PreparedLanes, tables) == 0 && offset_of!(PreparedLanes, valid) == 64);
    assert!(offset_of!(PreparedLanes, r_valid) == 72 && size_of::<PreparedLanes>() == 80);
};

unsafe extern "C" {
    fn ed25519_simd_prepare_chunk(
        scratch: *mut u8,
        inputs: &ChunkInputs<'_>,
        identity: &PointTable,
        lanes: *mut PreparedLanes<'_>,
    ) -> u32;
    fn ed25519_simd_dalek_prepare_chunk(
        scratch: *mut u8,
        inputs: &ChunkInputs<'_>,
        identity: &PointTable,
        lanes: *mut PreparedLanes<'_>,
    ) -> u32;
}

pub(crate) fn prepare_chunk<'a, P: VerificationPolicy>(
    inputs: &[VerifyInput<'_>; LANES],
    scratch: &'a mut MaybeUninit<ChunkScratch>,
) -> Option<(&'a ChunkScratch, PreparedLanes<'a>)> {
    let lanes = ChunkInputs {
        keys: inputs.each_ref().map(|input| &input.public_key),
        signatures: inputs.each_ref().map(|input| &input.signature),
    };
    let mut selected = MaybeUninit::uninit();
    let prepare = match P::POLICY {
        VerifyPolicy::Zip215 => ed25519_simd_prepare_chunk,
        VerifyPolicy::Dalek => ed25519_simd_dalek_prepare_chunk,
    };
    // SAFETY: the inputs remain readable for the call. Both outputs are
    // aligned, exclusive and disjoint. Success initializes every field,
    // including 0/1 eligibility bytes and references into scratch or identity.
    // A rejected chunk may leave partial outputs and exposes neither.
    unsafe {
        let ready = prepare(
            scratch.as_mut_ptr().cast(),
            &lanes,
            &IDENTITY_TABLE,
            selected.as_mut_ptr(),
        );
        (ready != 0).then(|| (scratch.assume_init_ref(), selected.assume_init()))
    }
}
