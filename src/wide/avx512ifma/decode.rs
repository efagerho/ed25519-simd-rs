use super::LANES;
use super::point::WidePoint;
use crate::batch::EncodedPointChunk;
use crate::edwards::PointTable;
use core::mem::MaybeUninit;

/// The eight affine R points returned by the paired key/signature decoder.
pub(crate) struct WideRPoint {
    pub(super) point: WidePoint,
}

/// The Dalek check reads the original low 255 input bits from the Y limbs.
pub(super) fn decompress_zip215<'a, const N: usize>(
    bytes: &[EncodedPointChunk; N],
    out: &'a mut MaybeUninit<[WidePoint; N]>,
) -> (&'a mut [WidePoint; N], [u8; N]) {
    const { assert!(N == 1 || N == 2) };
    const _: () = assert!(size_of::<EncodedPointChunk>() == 256);
    unsafe extern "C" {
        fn ed25519_simd_zip215_decode_r(
            out: *mut u8,
            encodings: *const EncodedPointChunk,
            chunks: usize,
        ) -> u16;
    }
    // SAFETY: the assembly reads N chunks and initializes every coordinate
    // of the aligned output, including lanes whose mask bit is clear.
    let (points, masks) = unsafe {
        let masks = ed25519_simd_zip215_decode_r(out.as_mut_ptr().cast(), bytes.as_ptr(), N);
        (out.assume_init_mut(), masks)
    };
    (points, core::array::from_fn(|i| (masks >> (8 * i)) as u8))
}

// Only decoded affine points reach this boundary. The assembly uses the
// caller's point storage as its running multiple and fills tables in place.
pub(super) fn build_key_tables<'a, const N: usize>(
    point: &mut WidePoint,
    out: &'a mut MaybeUninit<[PointTable; N]>,
) -> &'a [PointTable; N] {
    const { assert!(N == 1 || N == LANES) };
    unsafe extern "C" {
        fn ed25519_simd_build_key_tables(point: *mut u8, tables: *mut PointTable, count: usize);
    }
    // SAFETY: the decoder initializes every lane with Z=1 and 52-bit limbs.
    // The exclusive point and N contiguous output tables are disjoint. The
    // assembly writes all 17 entries of each table, including lane-zero mode.
    unsafe {
        ed25519_simd_build_key_tables(
            core::ptr::from_mut(point).cast(),
            out.as_mut_ptr().cast(),
            N,
        );
        out.assume_init_ref()
    }
}

pub(crate) struct DecodedKeys<'a> {
    pub(crate) tables: &'a [PointTable; LANES],
    pub(crate) valid: [bool; LANES],
    pub(crate) r: WideRPoint,
    pub(crate) r_valid: u8,
}

pub(crate) fn decode_keys_and_decompress_r<'a>(
    keys: &EncodedPointChunk,
    r_bytes: &EncodedPointChunk,
    out: &'a mut MaybeUninit<[PointTable; LANES]>,
) -> DecodedKeys<'a> {
    let mut storage = MaybeUninit::uninit();
    let ([key, r], [kmask, rmask]) = decompress_zip215(&[*keys, *r_bytes], &mut storage);
    DecodedKeys {
        tables: build_key_tables(key, out),
        valid: super::mask_to_lanes(kmask),
        r: WideRPoint { point: *r },
        r_valid: rmask,
    }
}
