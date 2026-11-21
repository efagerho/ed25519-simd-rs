mod decode;
mod field;
#[cfg_attr(
    all(feature = "asm", target_os = "linux", target_pointer_width = "64"),
    path = "ladder_step_asm.rs"
)]
mod ladder_step;
mod multiscalar;
mod point;
mod tables;
#[cfg(test)]
mod tests;
#[cfg_attr(
    all(feature = "asm", target_os = "linux", target_pointer_width = "64"),
    path = "zip215_asm.rs"
)]
pub(crate) mod zip215;

pub(crate) use decode::{WideRPoint, decode_keys_and_decompress_r, decode_public_key_table};
pub(crate) use multiscalar::{
    DALEK_BATCH, DalekCandidate, check_dalek_candidates, prepare_dalek_candidate,
    public_key_small_order_lanes, verify_prepared_dalek_decompressed_r,
};
pub(crate) use tables::build_basepoint_table_entries;

const LANES: usize = crate::batch::SIMD_LANES;
const _: () = assert!(LANES == 8, "avx512ifma assumes exactly 8 SIMD lanes");

/// Expand a per-lane bitmask into bools; shared with the scalar driver.
pub(crate) fn mask_to_lanes(mask: u8) -> [bool; LANES] {
    core::array::from_fn(|lane| (mask & (1 << lane)) != 0)
}
