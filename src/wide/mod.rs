use crate::batch::{R_ENCODING_LEN, SIMD_LANES};
use crate::edwards::PointTable;
use crate::scalar::Radix16;

/// Inputs available immediately after SHA-512, while all key tables are borrowed.
pub(crate) struct HashedChunk<'a> {
    pub(crate) public_key_tables: [&'a PointTable; SIMD_LANES],
    pub(crate) s_digits: &'a [Radix16; SIMD_LANES],
    pub(crate) digests: &'a [[u64; SIMD_LANES]; 8],
    pub(crate) r_bytes: &'a [[u8; R_ENCODING_LEN]; SIMD_LANES],
}

pub(crate) mod avx512ifma;
