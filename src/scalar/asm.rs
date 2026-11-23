#[cfg(test)]
use super::{LANES, Radix16};
#[cfg(test)]
use core::mem::MaybeUninit;

#[cfg(not(feature = "verify-asm-scalar"))]
core::arch::global_asm!(include_str!("reduce.S"), options(raw));
#[cfg(feature = "verify-asm-scalar")]
core::arch::global_asm!(
    include_str!(concat!(env!("OUT_DIR"), "/scalar-checked.S")),
    options(raw)
);
core::arch::global_asm!(include_str!("radix16.S"), options(raw));

#[cfg(test)]
unsafe extern "C" {
    pub(super) fn ed25519_simd_prepare_signature_scalars(
        out: *mut [Radix16; LANES],
        scalars: *const &[u8; 32],
    ) -> u8;
}

/// Prepare the signature scalars for the ladder and return their validity bits.
#[cfg(test)]
pub(crate) fn prepare_signature_scalars(scalars: [&[u8; 32]; LANES]) -> (u8, [Radix16; LANES]) {
    let mut out = MaybeUninit::uninit();
    // SAFETY: each pointer references 32 readable bytes. The disjoint output
    // receives 64 digit bytes per lane, including when its validity bit is clear.
    unsafe {
        let mask = ed25519_simd_prepare_signature_scalars(out.as_mut_ptr(), scalars.as_ptr());
        (mask, out.assume_init())
    }
}
