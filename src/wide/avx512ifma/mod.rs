use crate::batch::mask_to_lanes;

mod decode;
mod point;
mod post_hash_asm;
#[cfg(test)]
mod tests;

#[cfg(not(feature = "verify-asm-pow2"))]
core::arch::global_asm!(
    include_str!("pow22523.inc"),
    include_str!("pow2.S"),
    options(raw)
);

#[cfg(feature = "verify-asm-pow2")]
core::arch::global_asm!(include_str!(concat!(env!("OUT_DIR"), "/pow2-checked.S")));

core::arch::global_asm!(include_str!("stage_round.S"), options(raw));
core::arch::global_asm!(include_str!("ladder_step.S"), options(raw));
core::arch::global_asm!(include_str!("mul_s_base_minus_k_public.S"), options(raw));

pub(crate) use decode::decode_keys_and_decompress_r;
pub(crate) use post_hash_asm::{check_decoded, reject_small_order_keys};

const LANES: usize = crate::batch::SIMD_LANES;
const _: () = assert!(LANES == 8, "avx512ifma assumes exactly 8 SIMD lanes");
