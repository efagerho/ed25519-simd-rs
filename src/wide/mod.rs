use crate::batch::{R_ENCODING_LEN, SIMD_LANES};
use crate::edwards::PointTable;
use crate::scalar::Radix16;

/// Per-lane tables and scalar digits consumed by the SIMD verification ladder.
///
/// One radix-16 round selects a cached public-key multiple for
/// each lane, then updates all eight verification equations together.
pub(crate) struct PreparedChunk<'a> {
    pub(crate) public_key_tables: [&'a PointTable; SIMD_LANES],
    pub(crate) s_digits: &'a [Radix16; SIMD_LANES],
    pub(crate) k_digits: &'a [Radix16; SIMD_LANES],
}

/// Inputs available immediately after SHA-512, while all key tables are borrowed.
pub(crate) struct HashedChunk<'a> {
    pub(crate) public_key_tables: [&'a PointTable; SIMD_LANES],
    pub(crate) s_digits: &'a [Radix16; SIMD_LANES],
    pub(crate) digests: &'a [[u64; SIMD_LANES]; 8],
    pub(crate) r_bytes: &'a [[u8; R_ENCODING_LEN]; SIMD_LANES],
}

impl HashedChunk<'_> {
    pub(crate) fn with_digits<T>(&self, f: impl FnOnce(&PreparedChunk<'_>) -> T) -> T {
        let k_digits = crate::scalar::wide_words_to_radix16(self.digests);
        f(&PreparedChunk {
            public_key_tables: self.public_key_tables,
            s_digits: self.s_digits,
            k_digits: &k_digits,
        })
    }
}

pub(crate) mod avx512ifma;
