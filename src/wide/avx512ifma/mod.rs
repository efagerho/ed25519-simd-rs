mod point;
mod post_hash_asm;
mod prepare;
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

pub(crate) use post_hash_asm::check_decoded;
pub(crate) use prepare::{ChunkScratch, prepare_chunk};

const LANES: usize = crate::batch::SIMD_LANES;
const _: () = assert!(LANES == 8, "avx512ifma assumes exactly 8 SIMD lanes");
