use crate::field::Fe51;

/// Byte length of a compressed Edwards point encoding (sign bit + `y`).
pub(crate) const POINT_ENCODING_LEN: usize = 32;

/// The standard RFC 8032 encoding of the Ed25519 base point `B`.
const BASEPOINT_COMPRESSED: [u8; POINT_ENCODING_LEN] = [
    0x58, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
];

#[derive(Clone, Debug)]
pub(crate) struct EdwardsPoint {
    x: Fe51,
    y: Fe51,
    z: Fe51,
    t: Fe51,
}

// Signed-indexed layout: digit `d` maps to `entries[d + N]`, avoiding a hot
// unpredictable branch on the digit sign.
#[derive(Clone, Debug)]
pub(crate) struct PointTable {
    entries: [CachedPoint; SIGNED_POINT_TABLE_SIZE],
}

#[derive(Clone, Debug)]
pub(crate) struct BasepointTable {
    entries: [AffineCachedPoint; SIGNED_BASEPOINT_TABLE_SIZE],
}

// `base_pair_digit` folds two radix-16 digits into a radix-256 digit with
// maximum magnitude `8 + 8*16 = 136`.
const POINT_TABLE_SIZE: usize = 8;
const SIGNED_POINT_TABLE_SIZE: usize = 2 * POINT_TABLE_SIZE + 1;
const BASEPOINT_TABLE_SIZE: usize = 136;
const SIGNED_BASEPOINT_TABLE_SIZE: usize = 2 * BASEPOINT_TABLE_SIZE + 1;

#[derive(Clone, Debug)]
pub(crate) struct CachedPoint {
    y_plus_x: Fe51,
    y_minus_x: Fe51,
    z2: Fe51,
    t2d: Fe51,
}

impl CachedPoint {
    fn new(point: &EdwardsPoint) -> Self {
        Self {
            y_plus_x: point.y.add(&point.x),
            y_minus_x: point.y.subtract(&point.x),
            z2: point.z.double(),
            t2d: point.t.multiply(&Fe51::two_d()),
        }
    }

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

    pub(crate) fn identity() -> Self {
        Self::new(&EdwardsPoint::identity())
    }

    /// Cached form of `-P`: swap `y+x`/`y-x` and negate `t*2d`; `z2` is unchanged.
    fn negate(&self) -> Self {
        Self {
            y_plus_x: self.y_minus_x,
            y_minus_x: self.y_plus_x,
            z2: self.z2,
            t2d: self.t2d.negate(),
        }
    }
}

/// Affine cached precomputed point: the basepoint multiples are normalized to
/// `Z = 1` at table construction, so the projective `z2 = 2·Z` field collapses
/// to the constant `2` and is dropped. In the ladder the `Z₁·z2` product of a
/// mixed addition then becomes a doubling of the accumulator's `Z` — 7 M per
/// add instead of 8 — and the table is 25 % smaller (3 fields, not 4).
#[derive(Clone, Debug)]
pub(crate) struct AffineCachedPoint {
    y_plus_x: Fe51,
    y_minus_x: Fe51,
    t2d: Fe51,
}

impl AffineCachedPoint {
    /// Build from affine coordinates (`Z = 1`): `t = x·y`, so `t2d = 2d·x·y`.
    fn from_affine(x: &Fe51, y: &Fe51) -> Self {
        Self {
            y_plus_x: y.add(x),
            y_minus_x: y.subtract(x),
            t2d: x.multiply(y).multiply(&Fe51::two_d()),
        }
    }

    /// Affine identity `(x, y) = (0, 1)`.
    fn identity() -> Self {
        Self {
            y_plus_x: Fe51::one(),
            y_minus_x: Fe51::one(),
            t2d: Fe51::zero(),
        }
    }

    /// Cached form of `-P`: swap `y+x`/`y-x` and negate `t2d` (no `z2` to touch).
    fn negate(&self) -> Self {
        Self {
            y_plus_x: self.y_minus_x,
            y_minus_x: self.y_plus_x,
            t2d: self.t2d.negate(),
        }
    }

    pub(crate) fn coords(&self) -> (&Fe51, &Fe51, &Fe51) {
        (&self.y_plus_x, &self.y_minus_x, &self.t2d)
    }
}

/// Montgomery batch inversion of the `Z` coordinates, then normalize each point
/// to affine cached form. One field inversion for the whole table.
fn to_affine_cached_batch<const N: usize>(points: &[EdwardsPoint; N]) -> [AffineCachedPoint; N] {
    // Forward pass: zinv[i] holds the running product of Z[0..i].
    let mut zinv: [Fe51; N] = core::array::from_fn(|_| Fe51::one());
    let mut acc = Fe51::one();
    for i in 0..N {
        zinv[i] = acc;
        acc = acc.multiply(&points[i].z);
    }
    // Single inversion of the full product, then backward pass distributes it.
    acc = acc.invert();
    for i in (0..N).rev() {
        zinv[i] = zinv[i].multiply(&acc);
        acc = acc.multiply(&points[i].z);
    }
    core::array::from_fn(|i| {
        let x = points[i].x.multiply(&zinv[i]);
        let y = points[i].y.multiply(&zinv[i]);
        AffineCachedPoint::from_affine(&x, &y)
    })
}

impl PointTable {
    pub(crate) fn from_cached(
        cached_points: [CachedPoint; POINT_TABLE_SIZE],
        negative_cached_points: [CachedPoint; POINT_TABLE_SIZE],
        identity_cached: CachedPoint,
    ) -> Self {
        let entries = signed_entries(cached_points, negative_cached_points, identity_cached);
        Self { entries }
    }

    pub(crate) fn new(point: &EdwardsPoint) -> Self {
        let points = multiples_of(point);
        let cached_points: [CachedPoint; POINT_TABLE_SIZE] =
            core::array::from_fn(|i| CachedPoint::new(&points[i]));
        let negative_cached_points = core::array::from_fn(|i| cached_points[i].negate());
        let identity_cached = CachedPoint::new(&EdwardsPoint::identity());
        Self::from_cached(cached_points, negative_cached_points, identity_cached)
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
    pub(crate) fn new() -> Self {
        // Built once per process (see BASE_TABLE in verifier.rs), so there's
        // no reason to special-case even m via double() to save a handful of
        // multiplies: this whole computation runs once ever.
        let basepoint = EdwardsPoint::basepoint();
        let mut points: [EdwardsPoint; BASEPOINT_TABLE_SIZE] =
            core::array::from_fn(|_| basepoint.clone());
        for i in 1..BASEPOINT_TABLE_SIZE {
            points[i] = points[i - 1].add(&basepoint);
        }
        // Normalize all multiples to affine cached form with one batch inversion.
        let affine_points = to_affine_cached_batch(&points);
        let negative_points: [AffineCachedPoint; BASEPOINT_TABLE_SIZE] =
            core::array::from_fn(|i| affine_points[i].negate());
        let identity = AffineCachedPoint::identity();
        let entries = signed_entries(affine_points, negative_points, identity);
        Self { entries }
    }

    /// Select the affine point for a signed digit in
    /// `-BASEPOINT_TABLE_SIZE..=BASEPOINT_TABLE_SIZE`.
    pub(crate) fn select_signed_affine_ref(&self, digit: i16) -> &AffineCachedPoint {
        debug_assert!(
            (-(BASEPOINT_TABLE_SIZE as i16)..=(BASEPOINT_TABLE_SIZE as i16)).contains(&digit)
        );
        // SAFETY: `base_pair_digit` bounds `digit` to
        // `-BASEPOINT_TABLE_SIZE..=BASEPOINT_TABLE_SIZE`.
        unsafe {
            self.entries
                .get_unchecked((digit + BASEPOINT_TABLE_SIZE as i16) as usize)
        }
    }
}

/// Lay out `2N+1` table entries in signed-digit order: negatives `[-N..-1]`
/// descending, identity at the center, positives `[1..N]` ascending. Generic
/// over the entry type so both `CachedPoint` (projective) and
/// `AffineCachedPoint` tables share the layout.
fn signed_entries<T: Clone, const N: usize, const OUT: usize>(
    positives: [T; N],
    negatives: [T; N],
    identity: T,
) -> [T; OUT] {
    debug_assert_eq!(OUT, 2 * N + 1);
    core::array::from_fn(|i| {
        if i < N {
            negatives[N - 1 - i].clone()
        } else if i == N {
            identity.clone()
        } else {
            positives[i - N - 1].clone()
        }
    })
}

impl EdwardsPoint {
    pub(crate) fn identity() -> Self {
        Self {
            x: Fe51::zero(),
            y: Fe51::one(),
            z: Fe51::one(),
            t: Fe51::zero(),
        }
    }

    pub(crate) fn basepoint() -> Self {
        // Built once per process (see BASE_TABLE in verifier.rs), so a
        // decompress here (instead of hardcoded limb constants) costs
        // nothing worth avoiding.
        Self::decompress(&BASEPOINT_COMPRESSED).expect("basepoint encoding is valid")
    }

    pub(crate) fn decompress(bytes: &[u8; POINT_ENCODING_LEN]) -> Option<Self> {
        let x_sign = (bytes[31] >> 7) != 0;
        let mut y_bytes = *bytes;
        y_bytes[31] &= 0x7f;
        // ZIP-215/Dalek decoding treats y modulo p.
        let y = Fe51::from_bytes_unchecked(&y_bytes);

        let yy = y.square();
        let u = yy.subtract(&Fe51::one());
        let v = Fe51::one().add(&Fe51::d().multiply(&yy));
        let mut x = Fe51::sqrt_ratio(&u, &v)?;

        // For x == 0, negation is a no-op; signed zero is accepted.
        if x.is_odd() != x_sign {
            x = x.negate();
        }

        Some(Self {
            x,
            y,
            z: Fe51::one(),
            t: x.multiply(&y),
        })
    }

    pub(crate) fn add(&self, rhs: &Self) -> Self {
        let a = self.y.subtract(&self.x).multiply(&rhs.y.subtract(&rhs.x));
        let b = self.y.add(&self.x).multiply(&rhs.y.add(&rhs.x));
        let c = self.t.multiply(&rhs.t).multiply(&Fe51::two_d());
        let d = self.z.multiply(&rhs.z).double();
        let e = b.subtract(&a);
        let f = d.subtract(&c);
        let g = d.add(&c);
        let h = b.add(&a);

        Self {
            x: e.multiply(&f),
            y: g.multiply(&h),
            t: e.multiply(&h),
            z: f.multiply(&g),
        }
    }

    pub(crate) fn double(&self) -> Self {
        let a = self.x.square();
        let b = self.y.square();
        let c = self.z.square().double();
        let d = a.negate();
        let e = self.x.add(&self.y).square().subtract(&a).subtract(&b);
        let g = d.add(&b);
        let f = g.subtract(&c);
        let h = d.subtract(&b);

        Self {
            x: e.multiply(&f),
            y: g.multiply(&h),
            t: e.multiply(&h),
            z: f.multiply(&g),
        }
    }

    #[cfg(test)]
    pub(crate) fn coords(&self) -> (&Fe51, &Fe51, &Fe51, &Fe51) {
        (&self.x, &self.y, &self.z, &self.t)
    }

    #[cfg(test)]
    pub(crate) fn from_coords_unchecked(x: Fe51, y: Fe51, z: Fe51, t: Fe51) -> Self {
        Self { x, y, z, t }
    }

    #[cfg(test)]
    pub(crate) fn subtract(&self, rhs: &Self) -> Self {
        self.add(&rhs.negate())
    }

    #[cfg(test)]
    pub(crate) fn negate(&self) -> Self {
        Self {
            x: self.x.negate(),
            y: self.y,
            z: self.z,
            t: self.t.negate(),
        }
    }

    #[cfg(test)]
    pub(crate) fn compress(&self) -> [u8; POINT_ENCODING_LEN] {
        let zinv = self.z.invert();
        let x = self.x.multiply(&zinv);
        let y = self.y.multiply(&zinv);
        let mut bytes = y.to_bytes();
        bytes[31] |= (x.is_odd() as u8) << 7;
        bytes
    }
}

fn multiples_of(point: &EdwardsPoint) -> [EdwardsPoint; POINT_TABLE_SIZE] {
    let p2 = point.double();
    let p3 = p2.add(point);
    let p4 = p2.double();
    let p5 = p4.add(point);
    let p6 = p3.double();
    let p7 = p6.add(point);
    let p8 = p4.double();
    [point.clone(), p2, p3, p4, p5, p6, p7, p8]
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Golden equivalence (Phase 1a): every entry of the affine-cached basepoint
    /// table must represent exactly `[d]B` for its signed digit `d`. Cross-checks
    /// the batch-inversion normalization against an independent projective
    /// reference computed by repeated addition — the "old table" the affine one
    /// replaces. Covers identity (`d = 0`), all positives, and all negatives.
    #[test]
    fn affine_basepoint_table_matches_projective_multiples() {
        let table = BasepointTable::new();
        let basepoint = EdwardsPoint::basepoint();

        // Reference [1]B..[N]B built projectively, independent of the table path.
        let mut multiples = vec![basepoint.clone()];
        for _ in 1..BASEPOINT_TABLE_SIZE {
            multiples.push(multiples.last().unwrap().add(&basepoint));
        }

        let n = BASEPOINT_TABLE_SIZE as i16;
        for d in -n..=n {
            let reference = if d == 0 {
                EdwardsPoint::identity()
            } else {
                let m = multiples[(d.unsigned_abs() as usize) - 1].clone();
                if d < 0 { m.negate() } else { m }
            };
            // Normalize the reference to affine and derive its cached fields.
            let zinv = reference.z.invert();
            let x = reference.x.multiply(&zinv);
            let y = reference.y.multiply(&zinv);
            let expect_ypx = y.add(&x);
            let expect_ymx = y.subtract(&x);
            let expect_t2d = x.multiply(&y).multiply(&Fe51::two_d());

            let (ypx, ymx, t2d) = table.select_signed_affine_ref(d).coords();
            assert!(ypx.equals(&expect_ypx), "y+x mismatch at digit {d}");
            assert!(ymx.equals(&expect_ymx), "y-x mismatch at digit {d}");
            assert!(t2d.equals(&expect_t2d), "t2d mismatch at digit {d}");
        }
    }
}
