use crate::field::LIMB_COUNT;
use std::arch::x86_64::__m512i;

/// Eight field elements packed by limb for AVX-512 IFMA arithmetic.
///
/// `limbs[0]` contains the low limb of eight independent values,
/// so one vector multiply advances eight point operations at once.
#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct WideFe {
    pub(super) limbs: [__m512i; LIMB_COUNT],
}

/// Eight extended Edwards points packed coordinate-wise for SIMD arithmetic.
///
/// One ladder round doubles eight accumulators and adds eight
/// table-selected multiples with the same sequence of vector instructions.
#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct WidePoint {
    pub(super) x: WideFe,
    pub(super) y: WideFe,
    pub(super) z: WideFe,
    pub(super) t: WideFe,
}

// The assembly ABI is four consecutive fields, each containing five vectors.
// Check both the nested layout and every coordinate offset at compile time.
const _: () = {
    use core::mem::{align_of, offset_of, size_of};
    assert!(size_of::<WideFe>() == 320);
    assert!(align_of::<WideFe>() == 64);
    assert!(offset_of!(WideFe, limbs) == 0);
    assert!(size_of::<WidePoint>() == 1280);
    assert!(align_of::<WidePoint>() == 64);
    assert!(offset_of!(WidePoint, x) == 0);
    assert!(offset_of!(WidePoint, y) == 320);
    assert!(offset_of!(WidePoint, z) == 640);
    assert!(offset_of!(WidePoint, t) == 960);
};

#[cfg(not(feature = "verify-asm-double4"))]
core::arch::global_asm!(include_str!("double4.S"), options(raw));

#[cfg(feature = "verify-asm-double4")]
core::arch::global_asm!(include_str!(concat!(env!("OUT_DIR"), "/double4-checked.S")));

#[cfg(not(feature = "verify-asm-cached-add"))]
core::arch::global_asm!(include_str!("add_cached.S"), options(raw));

#[cfg(feature = "verify-asm-cached-add")]
core::arch::global_asm!(include_str!(concat!(
    env!("OUT_DIR"),
    "/cached-add-checked.S"
)));

// These entries share private IFMA field kernels and the encoded-point layout.
core::arch::global_asm!(
    include_str!("torsion.S"),
    include_str!("pow22523.inc"),
    include_str!("point_encoding.inc"),
    include_str!("dalek_recompress.S"),
    include_str!("post_hash.inc"),
    include_str!("zip215.S"),
    include_str!("dalek.S"),
    include_str!("key_table.S"),
    include_str!("decompress_r.S"),
    options(raw)
);
