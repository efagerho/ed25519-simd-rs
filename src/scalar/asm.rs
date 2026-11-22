use super::{LANES, Radix16, WIDE_WORDS};
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
