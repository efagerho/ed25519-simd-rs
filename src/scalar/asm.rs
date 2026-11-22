use super::{LANES, Radix16, WIDE_WORDS};
#[cfg(test)]
use core::mem::MaybeUninit;
use core::mem::size_of;

#[cfg(not(feature = "verify-asm-scalar"))]
core::arch::global_asm!(include_str!("reduce.S"), options(raw));
#[cfg(feature = "verify-asm-scalar")]
core::arch::global_asm!(
    include_str!(concat!(env!("OUT_DIR"), "/scalar-checked.S")),
    options(raw)
);
core::arch::global_asm!(include_str!("radix16.S"), options(raw));

const _: () = {
    assert!(LANES == 8 && WIDE_WORDS == 8);
    assert!(size_of::<Radix16>() == 64);
};

#[cfg(test)]
unsafe extern "C" {
    pub(super) fn ed25519_simd_digest_to_radix16(out: *mut u8, words: *const u8);

    pub(super) fn ed25519_simd_scalar_reduce_ifma(out: *mut u8, words: *const u8);
}

#[cfg(test)]
pub(super) fn wide_words_to_radix16(words: &[[u64; LANES]; WIDE_WORDS]) -> [Radix16; LANES] {
    let mut out = MaybeUninit::<[Radix16; LANES]>::uninit();
    // The pointers cover disjoint 512-byte buffers. The assembly accepts
    // unaligned addresses and writes all 64 digit bytes in every lane.
    unsafe {
        ed25519_simd_digest_to_radix16(out.as_mut_ptr().cast(), words.as_ptr().cast());
        out.assume_init()
    }
}
