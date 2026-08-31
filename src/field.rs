const LIMB_BITS: usize = 51;
const MASK: u64 = (1u64 << LIMB_BITS) - 1;
// Number of 51-bit limbs needed to represent a value modulo p = 2^255 - 19.
pub(crate) const LIMB_COUNT: usize = 5;

// 51-bit curve constants broadcast by the SIMD field path.
pub(crate) const D_LIMBS: [u64; LIMB_COUNT] = [
    929_955_233_495_203,
    466_365_720_129_213,
    1_662_059_464_998_953,
    2_033_849_074_728_123,
    1_442_794_654_840_575,
];
pub(crate) const TWO_D_LIMBS: [u64; LIMB_COUNT] = [
    1_859_910_466_990_425,
    932_731_440_258_426,
    1_072_319_116_312_658,
    1_815_898_335_770_999,
    633_789_495_995_903,
];
pub(crate) const SQRT_M1_LIMBS: [u64; LIMB_COUNT] = [
    1_718_705_420_411_056,
    234_908_883_556_509,
    2_233_514_472_574_048,
    2_117_202_627_021_982,
    765_476_049_583_133,
];
/// A field element modulo `2^255 - 19`, stored as five little-endian 51-bit limbs.
///
/// Field multiplication can accumulate products limbwise, then
/// fold an overflow of `2^255` back into the low limb as `19`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Fe51 {
    limbs: [u64; LIMB_COUNT],
}

impl Fe51 {
    /// Store limbs without canonicalizing. Valid only when each limb is already
    /// `< 2^52` (the loosely-reduced invariant), e.g. straight from a wide reduce.
    pub(crate) fn from_limbs_unchecked(limbs: [u64; LIMB_COUNT]) -> Self {
        debug_assert!(limbs.iter().all(|&limb| limb < (1u64 << 52)));
        Self { limbs }
    }

    pub(crate) const fn zero() -> Self {
        Self {
            limbs: [0; LIMB_COUNT],
        }
    }

    pub(crate) const fn one() -> Self {
        Self {
            limbs: [1, 0, 0, 0, 0],
        }
    }

    pub(crate) const fn two() -> Self {
        Self {
            limbs: [2, 0, 0, 0, 0],
        }
    }

    // "Unchecked" means canonicality only; limb masking still yields `< 2^51`
    // limbs, safe for every field op here.
    pub(crate) fn from_bytes_unchecked(bytes: &[u8; 32]) -> Self {
        Self {
            limbs: [
                load_u64_le(bytes, 0) & MASK,
                (load_u64_le(bytes, 6) >> 3) & MASK,
                (load_u64_le(bytes, 12) >> 6) & MASK,
                (load_u64_le(bytes, 19) >> 1) & MASK,
                (load_u64_le(bytes, 24) >> 12) & MASK,
            ],
        }
    }

    /// Loosely reduced limbs for AVX-512 IFMA field arithmetic.
    pub(crate) fn loose_limbs(&self) -> [u64; LIMB_COUNT] {
        debug_assert!(self.limbs.iter().all(|&limb| limb < (1u64 << 52)));
        self.limbs
    }
}

fn load_u64_le(bytes: &[u8; 32], offset: usize) -> u64 {
    u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
}
