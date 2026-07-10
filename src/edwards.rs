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
    /// `true` iff every entry is affine (`Z = 1`, so `z2 = 2`). Set by
    /// [`PointTable::normalized_affine`] for retained hot-key tables; the ladder
    /// uses the cheaper affine mixed-add only when all 8 lanes are affine.
    affine: bool,
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
        Self {
            entries,
            affine: false,
        }
    }

    /// Whether every entry is affine (`Z = 1`); see [`PointTable::affine`].
    pub(crate) fn is_affine(&self) -> bool {
        self.affine
    }

    /// Normalize all entries to affine (`Z = 1`) form with one batch inversion,
    /// so the ladder's mixed addition can double the accumulator's `Z` instead
    /// of multiplying by `z2`. Called once per key on insert into a retaining
    /// cache; the `NullKeyCache` single-use path never pays this.
    ///
    /// Each entry stores `z2 = 2·Z`, so `1/Z = 2·z2⁻¹`. Scaling `y±x` and `t2d`
    /// by `1/Z` and setting `z2 = 2` yields the affine cached point.
    pub(crate) fn normalized_affine(&self) -> Self {
        let mut z2_inv: [Fe51; SIGNED_POINT_TABLE_SIZE] =
            core::array::from_fn(|_| Fe51::one());
        let mut acc = Fe51::one();
        for i in 0..SIGNED_POINT_TABLE_SIZE {
            z2_inv[i] = acc;
            acc = acc.multiply(&self.entries[i].z2);
        }
        acc = acc.invert();
        for i in (0..SIGNED_POINT_TABLE_SIZE).rev() {
            z2_inv[i] = z2_inv[i].multiply(&acc);
            acc = acc.multiply(&self.entries[i].z2);
        }
        let two = Fe51::one().double();
        let entries = core::array::from_fn(|i| {
            let e = &self.entries[i];
            let z_inv = z2_inv[i].double(); // 1/Z = 2·z2⁻¹
            CachedPoint::from_fields(
                e.y_plus_x.multiply(&z_inv),
                e.y_minus_x.multiply(&z_inv),
                two,
                e.t2d.multiply(&z_inv),
            )
        });
        Self {
            entries,
            affine: true,
        }
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

    /// Recover the table's base point from its digit-1 entry. The cached
    /// fields give `y+x`, `y−x`, `2Z`, so `(2X : 2Y : 2Z)` — a valid
    /// projective representative of the point (extended coordinates are
    /// projective). The input `T` is set to zero: `double()` never reads it,
    /// and the Phase 2h consumer immediately doubles, which recomputes `T`.
    /// Valid for both projective and affine-normalized (1b) tables.
    pub(crate) fn recover_base_point(&self) -> EdwardsPoint {
        let one = self.select_signed_cached_ref(1);
        EdwardsPoint {
            x: one.y_plus_x.subtract(&one.y_minus_x), // 2X
            y: one.y_plus_x.add(&one.y_minus_x),      // 2Y
            z: one.z2,                                // 2Z
            t: Fe51::zero(),
        }
    }
}

impl BasepointTable {
    pub(crate) fn new() -> Self {
        Self::from_point(&EdwardsPoint::basepoint())
    }

    /// Build the 273-entry signed affine table for an arbitrary fixed base.
    /// Used for `B` itself and for `B′ = [2¹²⁷]B` (Phase 2h split ladder).
    pub(crate) fn from_point(base: &EdwardsPoint) -> Self {
        // Built once per process (see BASE_TABLE / BASE_TABLE_PRIME in
        // verifier.rs), so there's no reason to special-case even m via
        // double() to save a handful of multiplies: this runs once ever.
        let mut points: [EdwardsPoint; BASEPOINT_TABLE_SIZE] =
            core::array::from_fn(|_| base.clone());
        for i in 1..BASEPOINT_TABLE_SIZE {
            points[i] = points[i - 1].add(base);
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

    /// `[2¹²⁷]·self` by 127 doublings — the Phase 2h split-table base
    /// (`A′ = [2¹²⁷]A` at cache insert, `B′ = [2¹²⁷]B` once per process).
    /// Note `double()` ignores the input `t`, so a zero-`t` representative
    /// from `PointTable::recover_base_point` is a valid starting point; the
    /// result carries a correct `t` from the final doubling.
    pub(crate) fn mul_by_pow2_127(&self) -> Self {
        let mut p = self.double();
        for _ in 1..127 {
            p = p.double();
        }
        p
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

    /// Extended coordinates; production use: lane-packing for the Phase 2h
    /// SIMD promotion pass (`WidePoint::from_points`).
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

    /// Phase 2h: recovering a table's base point from its digit-1 entry must
    /// round-trip, for projective and affine-normalized (1b) tables, on
    /// ordinary and small-order points. (`T` is not recovered; `compress`
    /// only needs `x, y, z`.)
    #[test]
    fn recover_base_point_roundtrips() {
        // An order-8 point (torsion recovery must work too — ZIP-215 keys).
        let ord8 = EdwardsPoint::decompress(&[
            0x26, 0xe8, 0x95, 0x8f, 0xc2, 0xb2, 0x27, 0xb0, 0x45, 0xc3, 0xf4, 0x89, 0xf2, 0xef,
            0x98, 0xf0, 0xd5, 0xdf, 0xac, 0x05, 0xd3, 0xc6, 0x33, 0x39, 0xb1, 0x38, 0x02, 0x88,
            0x6d, 0x53, 0xfc, 0x05,
        ])
        .expect("order-8 point decodes");
        for point in [
            EdwardsPoint::basepoint(),
            EdwardsPoint::basepoint().double(),
            EdwardsPoint::identity(),
            ord8,
        ] {
            let projective = PointTable::new(&point);
            assert_eq!(
                projective.recover_base_point().compress(),
                point.compress(),
                "projective-table recovery diverged"
            );
            assert_eq!(
                projective.normalized_affine().recover_base_point().compress(),
                point.compress(),
                "affine-table recovery diverged"
            );
        }
    }

    /// Phase 2h golden: the generalized fixed-base table for `B′ = [2¹²⁷]B`
    /// must hold exactly `[d]B′` at every signed digit — the 1a golden shape
    /// applied to `from_point` (batch-inversion normalization vs an
    /// independent per-entry projective reference).
    #[test]
    fn affine_table_from_point_matches_multiples_of_b_prime() {
        let b_prime = EdwardsPoint::basepoint().mul_by_pow2_127();
        let table = BasepointTable::from_point(&b_prime);

        let mut multiples = vec![b_prime.clone()];
        for _ in 1..BASEPOINT_TABLE_SIZE {
            multiples.push(multiples.last().unwrap().add(&b_prime));
        }
        let n = BASEPOINT_TABLE_SIZE as i16;
        for d in -n..=n {
            let reference = if d == 0 {
                EdwardsPoint::identity()
            } else {
                let m = multiples[(d.unsigned_abs() as usize) - 1].clone();
                if d < 0 { m.negate() } else { m }
            };
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

    /// Golden equivalence (Phase 1b): normalizing a projective public-key table
    /// to affine must preserve every entry's point. Each affine entry equals the
    /// projective one divided by `Z = z2/2`; verified by cross-multiplication
    /// (`affine · z2 == 2 · projective`) so the check is independent of `invert`.
    /// Uses the basepoint's radix-16 table, whose multiples `[2..8]B` have `Z ≠ 1`.
    #[test]
    fn normalized_affine_pointtable_matches_projective() {
        let projective = PointTable::new(&EdwardsPoint::basepoint());
        let affine = projective.normalized_affine();
        assert!(affine.is_affine());
        assert!(!projective.is_affine());

        let two = Fe51::one().double();
        for d in -8..=8i8 {
            let (pypx, pymx, pz2, pt2d) = projective.select_signed_cached_ref(d).coords();
            let (aypx, aymx, az2, at2d) = affine.select_signed_cached_ref(d).coords();
            assert!(az2.equals(&two), "affine z2 != 2 at digit {d}");
            assert!(
                aypx.multiply(pz2).equals(&pypx.double()),
                "y+x mismatch at digit {d}"
            );
            assert!(
                aymx.multiply(pz2).equals(&pymx.double()),
                "y-x mismatch at digit {d}"
            );
            assert!(
                at2d.multiply(pz2).equals(&pt2d.double()),
                "t2d mismatch at digit {d}"
            );
        }
    }
}
