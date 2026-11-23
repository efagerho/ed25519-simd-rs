mod point;
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

pub(crate) use prepare::ChunkScratch;
