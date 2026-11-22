/// A scalar encoded as 64 little-endian signed radix-16 digits in `-8..=7`.
///
/// `28 = -4 + 2*16`, so a point ladder can use the digits `-4`
/// and `2` to select precomputed multiples instead of adding the point 28 times.
pub(crate) type Radix16 = [i8; 64];
const LANES: usize = crate::batch::SIMD_LANES;
const WIDE_WORDS: usize = 8;

mod asm;
#[cfg(test)]
pub(crate) use asm::prepare_signature_scalars;
#[cfg(test)]
mod tests;
#[cfg(test)]
#[path = "wide/tests.rs"]
mod wide_tests;
