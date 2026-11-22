use super::LANES;
use super::point::WidePoint;
use super::tables::{build_lane0_table_from_point, build_tables_from_point};
use crate::batch::EncodedPointChunk;
use crate::edwards::PointTable;
use crate::input::PUBLIC_KEY_LEN;
use core::mem::MaybeUninit;

/// The eight affine R points returned by the paired key/signature decoder.
pub(crate) struct WideRPoint {
    pub(super) point: WidePoint,
}

/// The Dalek check reads the original low 255 input bits from the Y limbs.
pub(super) fn decompress_zip215<'a, const N: usize>(
    bytes: &[EncodedPointChunk; N],
    out: &'a mut MaybeUninit<[WidePoint; N]>,
) -> (&'a [WidePoint; N], [u8; N]) {
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
        (out.assume_init_ref(), masks)
    };
    (points, core::array::from_fn(|i| (masks >> (8 * i)) as u8))
}

pub(crate) fn decode_keys_and_decompress_r(
    keys: &EncodedPointChunk,
    r_bytes: &EncodedPointChunk,
    key_tables: &mut [Option<PointTable>; LANES],
) -> (u8, WideRPoint, u8) {
    let mut storage = MaybeUninit::uninit();
    let ([key, r], [kmask, rmask]) = decompress_zip215(&[*keys, *r_bytes], &mut storage);
    build_tables_from_point(*key, key_tables);
    (kmask, WideRPoint { point: *r }, rmask)
}

pub(super) fn decompress_points_wide(bytes: &EncodedPointChunk) -> (WidePoint, u8) {
    let mut storage = MaybeUninit::uninit();
    let ([point], [mask]) = decompress_zip215(core::array::from_ref(bytes), &mut storage);
    (*point, mask)
}

/// Decode a single public key and materialize lane zero into its cached table.
pub(crate) fn decode_public_key_table(encoded: &[u8; PUBLIC_KEY_LEN]) -> Option<PointTable> {
    let (point, mask) = decompress_points_wide(&[*encoded; LANES]);
    (mask & 1 != 0).then(|| build_lane0_table_from_point(point))
}
