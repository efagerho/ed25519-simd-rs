mod decode;
mod field;
mod multiscalar;
mod point;
mod tables;
#[cfg(test)]
mod tests;

pub(crate) use decode::{WideRPoint, decode_keys_and_decompress_r, decode_public_key_table};
pub(crate) use multiscalar::{
    DALEK_BATCH, DalekCandidate, ZIP215_BATCH, Zip215Candidate, check_zip215_candidates,
    compress_dalek_candidates, prepare_dalek_candidate, prepare_zip215_candidate,
    public_key_small_order_lanes, verify_prepared_dalek_decompressed_r, verify_prepared_zip215,
};
pub(crate) use tables::build_basepoint_table_entries;

const LANES: usize = crate::batch::SIMD_LANES;
const _: () = assert!(LANES == 8, "avx512ifma assumes exactly 8 SIMD lanes");

/// Expand a per-lane bitmask into bools; shared with the scalar driver.
pub(crate) fn mask_to_lanes(mask: u8) -> [bool; LANES] {
    core::array::from_fn(|lane| (mask & (1 << lane)) != 0)
}
