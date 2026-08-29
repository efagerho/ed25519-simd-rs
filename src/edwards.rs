use crate::field::Fe51;

/// Byte length of a compressed Edwards point encoding (sign bit + `y`).
pub(crate) const POINT_ENCODING_LEN: usize = 32;

/// The standard RFC 8032 encoding of the Ed25519 base point `B`.
pub(crate) const BASEPOINT_COMPRESSED: [u8; POINT_ENCODING_LEN] = [
    0x58, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
];

// Signed-indexed layout: digit `d` maps to `entries[d + N]`, avoiding a hot
// unpredictable branch on the digit sign.
#[derive(Clone, Debug)]
pub(crate) struct PointTable {
    entries: [CachedPoint; SIGNED_POINT_TABLE_SIZE],
}

#[derive(Clone, Debug)]
pub(crate) struct BasepointTable {
    entries: Box<BasepointTableEntries>,
}

// `base_pair_digit` folds two radix-16 digits into a radix-256 digit with
// maximum magnitude `8 + 8*16 = 136`.
const POINT_TABLE_SIZE: usize = 8;
const SIGNED_POINT_TABLE_SIZE: usize = 2 * POINT_TABLE_SIZE + 1;
pub(crate) const BASEPOINT_TABLE_SIZE: usize = 136;
const SIGNED_BASEPOINT_TABLE_SIZE: usize = 2 * BASEPOINT_TABLE_SIZE + 1;
pub(crate) type BasepointTableEntries = [AffineCachedPoint; SIGNED_BASEPOINT_TABLE_SIZE];

#[derive(Clone, Debug)]
pub(crate) struct CachedPoint {
    y_plus_x: Fe51,
    y_minus_x: Fe51,
    z2: Fe51,
    t2d: Fe51,
}

impl CachedPoint {
    pub(crate) fn coords(&self) -> (&Fe51, &Fe51, &Fe51, &Fe51) {
        (&self.y_plus_x, &self.y_minus_x, &self.z2, &self.t2d)
    }

    /// Accept loosely-reduced fields (`< 2^52` per limb) from SIMD table
    /// construction; all consumers tolerate that bound.
    pub(crate) fn from_fields(y_plus_x: Fe51, y_minus_x: Fe51, z2: Fe51, t2d: Fe51) -> Self {
        Self {
            y_plus_x,
            y_minus_x,
            z2,
            t2d,
        }
    }

    pub(crate) const fn identity() -> Self {
        Self {
            y_plus_x: Fe51::one(),
            y_minus_x: Fe51::one(),
            z2: Fe51::two(),
            t2d: Fe51::zero(),
        }
    }
}

/// Affine cached point used by the fixed-base table. Since `Z = 1`, the
/// cached `2*Z` coordinate is the constant two and does not need to be stored.
#[derive(Clone, Debug)]
pub(crate) struct AffineCachedPoint {
    y_plus_x: Fe51,
    y_minus_x: Fe51,
    t2d: Fe51,
}

impl AffineCachedPoint {
    pub(crate) fn identity() -> Self {
        Self {
            y_plus_x: Fe51::one(),
            y_minus_x: Fe51::one(),
            t2d: Fe51::zero(),
        }
    }

    /// Accept loosely-reduced fields (`< 2^52` per limb) produced by the
    /// SIMD basepoint-table builder.
    pub(crate) fn from_fields(y_plus_x: Fe51, y_minus_x: Fe51, t2d: Fe51) -> Self {
        Self {
            y_plus_x,
            y_minus_x,
            t2d,
        }
    }

    pub(crate) fn coords(&self) -> (&Fe51, &Fe51, &Fe51) {
        (&self.y_plus_x, &self.y_minus_x, &self.t2d)
    }
}

impl PointTable {
    pub(crate) fn identity() -> Self {
        Self {
            entries: core::array::from_fn(|_| CachedPoint::identity()),
        }
    }

    /// Initialization-only copy kept separate from the verifier's hot SIMD
    /// table builder so extra setup call sites do not change its inlining.
    #[inline(never)]
    pub(crate) fn cold_identity() -> Self {
        Self {
            entries: core::array::from_fn(|_| CachedPoint::identity()),
        }
    }

    pub(crate) fn set_multiple(
        &mut self,
        multiple: usize,
        positive: CachedPoint,
        negative: CachedPoint,
    ) {
        debug_assert!((1..=POINT_TABLE_SIZE).contains(&multiple));
        self.entries[POINT_TABLE_SIZE + multiple] = positive;
        self.entries[POINT_TABLE_SIZE - multiple] = negative;
    }

    /// Select the cached point for a signed digit in `-8..=8`.
    pub(crate) fn select_signed_cached_ref(&self, digit: i8) -> &CachedPoint {
        debug_assert!((-8..=8).contains(&digit));
        // SAFETY: `digit` is a radix-16 digit in `-8..=8`, so `digit + 8` is
        // in bounds for this 17-entry table.
        unsafe { self.entries.get_unchecked((digit + 8) as usize) }
    }
}

impl BasepointTable {
    #[cold]
    pub(crate) fn new() -> Self {
        Self {
            entries: crate::wide::avx512ifma::build_basepoint_table_entries(),
        }
    }

    pub(crate) fn entries(&self) -> &BasepointTableEntries {
        &self.entries
    }
}

pub(crate) fn select_signed_affine_cached_ref(
    entries: &BasepointTableEntries,
    digit: i16,
) -> &AffineCachedPoint {
    debug_assert!(
        (-(BASEPOINT_TABLE_SIZE as i16)..=(BASEPOINT_TABLE_SIZE as i16)).contains(&digit)
    );
    // SAFETY: `base_pair_digit` bounds `digit` to
    // `-BASEPOINT_TABLE_SIZE..=BASEPOINT_TABLE_SIZE`.
    unsafe { entries.get_unchecked((digit + BASEPOINT_TABLE_SIZE as i16) as usize) }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A regression overflows this thread's stack, which aborts the whole
    /// test process (SIGSEGV) rather than failing just this test.
    #[test]
    fn basepoint_table_constructs_on_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| std::hint::black_box(BasepointTable::new()))
            .unwrap()
            .join()
            .unwrap();
    }
}
