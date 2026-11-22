mod decode;
mod field;
mod point;
mod post_hash_asm;
mod tables;
#[cfg(test)]
mod tests;

core::arch::global_asm!(include_str!("stage_round.S"), options(raw));
core::arch::global_asm!(include_str!("ladder_step.S"), options(raw));
core::arch::global_asm!(include_str!("mul_s_base_minus_k_public.S"), options(raw));

pub(crate) mod zip215 {
    pub(crate) type Queue = super::post_hash_asm::Queue<false>;
}
pub(crate) mod dalek {
    pub(crate) type Queue = super::post_hash_asm::Queue<true>;
    pub(crate) use super::post_hash_asm::reject_small_order_keys;
}

pub(crate) use decode::{WideRPoint, decode_keys_and_decompress_r, decode_public_key_table};

const LANES: usize = crate::batch::SIMD_LANES;
const _: () = assert!(LANES == 8, "avx512ifma assumes exactly 8 SIMD lanes");

/// Expand a per-lane bitmask into bools; shared with the scalar driver.
pub(crate) fn mask_to_lanes(mask: u8) -> [bool; LANES] {
    core::array::from_fn(|lane| (mask & (1 << lane)) != 0)
}
