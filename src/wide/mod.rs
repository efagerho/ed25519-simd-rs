use crate::batch::SIMD_LANES;
use crate::edwards::PointTable;
use crate::scalar::Radix16;

pub(crate) struct PreparedChunk<'a> {
    pub(crate) public_key_tables: [&'a PointTable; SIMD_LANES],
    pub(crate) s_digits: &'a [Radix16; SIMD_LANES],
    pub(crate) k_digits: &'a [Radix16; SIMD_LANES],
}

pub(crate) mod avx512ifma;
