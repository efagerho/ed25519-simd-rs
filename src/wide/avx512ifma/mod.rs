#[cfg(not(all(feature = "asm", target_os = "linux", target_pointer_width = "64")))]
pub(crate) mod dalek;
mod decode;
mod field;
#[cfg_attr(
    all(feature = "asm", target_os = "linux", target_pointer_width = "64"),
    path = "ladder_step_asm.rs"
)]
mod ladder_step;
#[cfg(any(
    test,
    not(all(feature = "asm", target_os = "linux", target_pointer_width = "64"))
))]
mod multiscalar;
mod point;
#[cfg(all(feature = "asm", target_os = "linux", target_pointer_width = "64"))]
mod post_hash_asm;
mod tables;
#[cfg(test)]
mod tests;
#[cfg(not(all(feature = "asm", target_os = "linux", target_pointer_width = "64")))]
pub(crate) mod zip215;
#[cfg(all(feature = "asm", target_os = "linux", target_pointer_width = "64"))]
pub(crate) mod zip215 {
    pub(crate) type Queue = super::post_hash_asm::Queue<false>;
}
#[cfg(all(feature = "asm", target_os = "linux", target_pointer_width = "64"))]
pub(crate) mod dalek {
    pub(crate) type Queue = super::post_hash_asm::Queue<true>;
    pub(crate) use super::post_hash_asm::reject_small_order_keys;
}

pub(crate) use decode::{WideRPoint, decode_keys_and_decompress_r, decode_public_key_table};
#[cfg(test)]
pub(crate) use multiscalar::{DALEK_BATCH, DalekCandidate, check_dalek_candidates};
pub(crate) use tables::build_basepoint_table_entries;

const LANES: usize = crate::batch::SIMD_LANES;
const _: () = assert!(LANES == 8, "avx512ifma assumes exactly 8 SIMD lanes");

/// Expand a per-lane bitmask into bools; shared with the scalar driver.
pub(crate) fn mask_to_lanes(mask: u8) -> [bool; LANES] {
    core::array::from_fn(|lane| (mask & (1 << lane)) != 0)
}
