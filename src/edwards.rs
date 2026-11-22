use crate::field::Fe51;

/// Byte length of a compressed Edwards point encoding (sign bit + `y`).
pub(crate) const POINT_ENCODING_LEN: usize = 32;

/// Precomputed signed multiples `[-8]P..=[8]P` for variable-base multiplication.
///
/// The signed-indexed layout avoids a hot branch: digit `-3`
/// directly selects `entries[-3 + 8]` for the next ladder addition.
pub(crate) struct PointTable {
    entries: [core::mem::MaybeUninit<CachedPoint>; SIGNED_POINT_TABLE_SIZE],
    #[cfg(debug_assertions)]
    initialized_entries: u32,
}

// The ladder folds two radix-16 digits into a radix-256 digit with
// maximum magnitude `8 + 8*16 = 136`.
const POINT_TABLE_SIZE: usize = 8;
const SIGNED_POINT_TABLE_SIZE: usize = 2 * POINT_TABLE_SIZE + 1;
#[cfg(debug_assertions)]
const ALL_POINT_TABLE_ENTRIES: u32 = (1 << SIGNED_POINT_TABLE_SIZE) - 1;
pub(crate) const BASEPOINT_TABLE_SIZE: usize = 136;
const SIGNED_BASEPOINT_TABLE_SIZE: usize = 2 * BASEPOINT_TABLE_SIZE + 1;
/// The signed `[-136]B..=[136]B` entries used by the radix-256 basepoint ladder.
///
/// A folded digit of `-12` directly indexes the cached `[-12]B`
/// entry, replacing several point additions with one lookup and one addition.
pub(crate) type BasepointTableEntries = [AffineCachedPoint; SIGNED_BASEPOINT_TABLE_SIZE];

/// Read-only affine cache for the fixed base point, in signed digit order.
pub(crate) static BASEPOINT_TABLE: BasepointTableEntries = {
    const fn entry(y_minus_x: [u64; 5], y_plus_x: [u64; 5], t2d: [u64; 5]) -> AffineCachedPoint {
        AffineCachedPoint {
            y_minus_x: Fe51::from_limbs_unchecked(y_minus_x),
            y_plus_x: Fe51::from_limbs_unchecked(y_plus_x),
            t2d: Fe51::from_limbs_unchecked(t2d),
        }
    }
    include!("edwards/basepoint_table.in")
};

/// A projective point in the form consumed by the extended Edwards addition
/// formula. Scalar multiplication repeatedly adds table-selected points; caching
/// `Y + X`, `Y - X`, `2Z`, and `2dT` avoids recomputing those values in every
/// hot-path addition, reducing each lookup-and-add to field multiplications and
/// additions with the accumulator.
///
/// After a ladder selects `[3]P`, these four cached coordinates
/// feed the extended-point addition without recomputing them from `P`.
#[repr(C)]
#[derive(Clone, Debug)]
pub(crate) struct CachedPoint {
    y_minus_x: Fe51,
    y_plus_x: Fe51,
    t2d: Fe51,
    z2: Fe51,
}

impl CachedPoint {
    #[cfg(test)]
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
/// Selecting `[20]B` supplies three cached fields while the mixed
/// addition doubles the accumulator's `Z` in place of loading a fourth field.
#[repr(C)]
#[derive(Clone, Debug)]
pub(crate) struct AffineCachedPoint {
    y_minus_x: Fe51,
    y_plus_x: Fe51,
    t2d: Fe51,
}

// stage_round.S transposes consecutive words from these exact entry layouts.
const _: () = {
    use core::mem::{align_of, offset_of, size_of};
    assert!(POINT_TABLE_SIZE == 8 && BASEPOINT_TABLE_SIZE == 136);
    assert!(size_of::<Fe51>() == 40 && align_of::<Fe51>() == 8);
    assert!(size_of::<CachedPoint>() == 160);
    assert!(offset_of!(CachedPoint, y_minus_x) == 0);
    assert!(offset_of!(CachedPoint, y_plus_x) == 40);
    assert!(offset_of!(CachedPoint, t2d) == 80);
    assert!(offset_of!(CachedPoint, z2) == 120);
    assert!(size_of::<AffineCachedPoint>() == 120);
    assert!(offset_of!(AffineCachedPoint, y_minus_x) == 0);
    assert!(offset_of!(AffineCachedPoint, y_plus_x) == 40);
    assert!(offset_of!(AffineCachedPoint, t2d) == 80);
};

#[cfg(test)]
impl AffineCachedPoint {
    pub(crate) fn identity() -> Self {
        Self {
            y_plus_x: Fe51::one(),
            y_minus_x: Fe51::one(),
            t2d: Fe51::zero(),
        }
    }

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
    /// Create a decode-time destination with only its identity slot filled.
    ///
    /// # Safety
    /// The caller must fill both signs of every multiple in `1..=8` with
    /// [`set_multiple`](Self::set_multiple) before the table is selected,
    /// cloned, retained, or otherwise exposed as a completed table.
    pub(crate) unsafe fn decode_destination() -> Self {
        let mut entries = [const { core::mem::MaybeUninit::uninit() }; SIGNED_POINT_TABLE_SIZE];
        entries[POINT_TABLE_SIZE].write(CachedPoint::identity());
        Self {
            entries,
            #[cfg(debug_assertions)]
            initialized_entries: 1 << POINT_TABLE_SIZE,
        }
    }

    #[inline(never)]
    pub(crate) fn identity() -> Self {
        Self {
            entries: core::array::from_fn(|_| core::mem::MaybeUninit::new(CachedPoint::identity())),
            #[cfg(debug_assertions)]
            initialized_entries: ALL_POINT_TABLE_ENTRIES,
        }
    }

    pub(crate) fn set_multiple(
        &mut self,
        multiple: usize,
        positive: CachedPoint,
        negative: CachedPoint,
    ) {
        debug_assert!((1..=POINT_TABLE_SIZE).contains(&multiple));
        self.entries[POINT_TABLE_SIZE + multiple].write(positive);
        self.entries[POINT_TABLE_SIZE - multiple].write(negative);
        #[cfg(debug_assertions)]
        {
            self.initialized_entries |=
                (1 << (POINT_TABLE_SIZE + multiple)) | (1 << (POINT_TABLE_SIZE - multiple));
        }
    }

    /// The contiguous entry array begins at [-8]P. The enclosing table also
    /// carries debug-only initialization state outside the assembly ABI.
    pub(crate) fn entries_ptr(&self) -> *const CachedPoint {
        self.debug_assert_fully_initialized();
        self.entries.as_ptr().cast()
    }

    /// Select the cached point for a signed digit in `-8..=8`.
    #[cfg(test)]
    pub(crate) fn select_signed_cached_ref(&self, digit: i8) -> &CachedPoint {
        debug_assert!((-8..=8).contains(&digit));
        self.debug_assert_fully_initialized();
        // SAFETY: `digit` is a radix-16 digit in `-8..=8`, so `digit + 8` is
        // in bounds for this 17-entry table.
        unsafe {
            self.entries
                .get_unchecked((digit + 8) as usize)
                .assume_init_ref()
        }
    }

    #[inline(always)]
    fn debug_assert_fully_initialized(&self) {
        #[cfg(debug_assertions)]
        debug_assert_eq!(self.initialized_entries, ALL_POINT_TABLE_ENTRIES);
    }
}

impl Clone for PointTable {
    fn clone(&self) -> Self {
        self.debug_assert_fully_initialized();
        Self {
            entries: core::array::from_fn(|index| {
                // SAFETY: tables are cloned only after decode construction or
                // by an all-identity constructor, both of which fill every slot.
                core::mem::MaybeUninit::new(unsafe {
                    self.entries[index].assume_init_ref().clone()
                })
            }),
            #[cfg(debug_assertions)]
            initialized_entries: ALL_POINT_TABLE_ENTRIES,
        }
    }
}

impl core::fmt::Debug for PointTable {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.debug_struct("PointTable").finish_non_exhaustive()
    }
}
