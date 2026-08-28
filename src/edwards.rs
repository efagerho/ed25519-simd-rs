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
    entries: Box<BasepointTableEntries>,
}

// `base_pair_digit` folds two radix-16 digits into a radix-256 digit with
// maximum magnitude `8 + 8*16 = 136`.
const POINT_TABLE_SIZE: usize = 8;
const SIGNED_POINT_TABLE_SIZE: usize = 2 * POINT_TABLE_SIZE + 1;
const BASEPOINT_TABLE_SIZE: usize = 136;
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

    pub(crate) const fn identity() -> Self {
        Self {
            y_plus_x: Fe51::one(),
            y_minus_x: Fe51::one(),
            z2: Fe51::two(),
            t2d: Fe51::zero(),
        }
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

/// Affine cached point used by the fixed-base table. Since `Z = 1`, the
/// cached `2*Z` coordinate is the constant two and does not need to be stored.
#[derive(Clone, Debug)]
pub(crate) struct AffineCachedPoint {
    y_plus_x: Fe51,
    y_minus_x: Fe51,
    t2d: Fe51,
}

impl AffineCachedPoint {
    fn from_affine(x: &Fe51, y: &Fe51) -> Self {
        Self {
            y_plus_x: y.add(x),
            y_minus_x: y.subtract(x),
            t2d: x.multiply(y).multiply(&Fe51::two_d()),
        }
    }

    fn identity() -> Self {
        Self {
            y_plus_x: Fe51::one(),
            y_minus_x: Fe51::one(),
            t2d: Fe51::zero(),
        }
    }

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

/// Normalize a table of projective points with one Montgomery batch inversion.
fn to_affine_cached_batch(points: &[EdwardsPoint]) -> Vec<AffineCachedPoint> {
    debug_assert!(
        points.iter().all(|point| !point.z.equals(&Fe51::zero())),
        "batch inversion requires every Z to be nonzero"
    );

    let mut prefixes = Vec::with_capacity(points.len());
    let mut product = Fe51::one();
    for point in points {
        prefixes.push(product);
        product = product.multiply(&point.z);
    }

    product = product.invert();
    for i in (0..points.len()).rev() {
        prefixes[i] = prefixes[i].multiply(&product);
        product = product.multiply(&points[i].z);
    }

    points
        .iter()
        .zip(prefixes)
        .map(|(point, zinv)| {
            let x = point.x.multiply(&zinv);
            let y = point.y.multiply(&zinv);
            AffineCachedPoint::from_affine(&x, &y)
        })
        .collect()
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
        Self::from_cached(
            cached_points,
            negative_cached_points,
            CachedPoint::identity(),
        )
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
        // One-time base-table setup does not need an even-multiple fast path.
        let basepoint = EdwardsPoint::basepoint();
        let mut points = Vec::with_capacity(BASEPOINT_TABLE_SIZE);
        points.push(basepoint.clone());
        for i in 1..BASEPOINT_TABLE_SIZE {
            points.push(points[i - 1].add(&basepoint));
        }
        let affine_points = to_affine_cached_batch(&points);
        // Heap-built copy of the `signed_entries` layout: negatives from
        // -136P down to -1P, identity, then 1P..136P.
        let mut entries = Vec::with_capacity(SIGNED_BASEPOINT_TABLE_SIZE);
        entries.extend(affine_points.iter().rev().map(AffineCachedPoint::negate));
        entries.push(AffineCachedPoint::identity());
        entries.extend(affine_points);
        let entries = entries
            .into_boxed_slice()
            .try_into()
            .unwrap_or_else(|_| unreachable!("basepoint table length is fixed"));
        Self { entries }
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

fn signed_entries<T: Clone, const N: usize, const OUT: usize>(
    cached_points: [T; N],
    negative_cached_points: [T; N],
    identity_cached: T,
) -> [T; OUT] {
    const {
        assert!(
            OUT == 2 * N + 1,
            "a signed digit table holds 2 * N + 1 entries"
        )
    };
    core::array::from_fn(|i| {
        if i < N {
            negative_cached_points[N - 1 - i].clone()
        } else if i == N {
            identity_cached.clone()
        } else {
            cached_points[i - N - 1].clone()
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
        // One-time base-table setup makes decompression negligible.
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

    #[test]
    fn affine_basepoint_table_matches_projective_multiples() {
        let table = BasepointTable::new();
        let basepoint = EdwardsPoint::basepoint();
        let mut multiples = vec![basepoint.clone()];
        for _ in 1..BASEPOINT_TABLE_SIZE {
            multiples.push(multiples.last().unwrap().add(&basepoint));
        }

        let n = BASEPOINT_TABLE_SIZE as i16;
        for digit in -n..=n {
            let point = if digit == 0 {
                EdwardsPoint::identity()
            } else {
                let point = multiples[digit.unsigned_abs() as usize - 1].clone();
                if digit < 0 { point.negate() } else { point }
            };
            let zinv = point.z.invert();
            let x = point.x.multiply(&zinv);
            let y = point.y.multiply(&zinv);
            let expected = AffineCachedPoint::from_affine(&x, &y);
            let actual = select_signed_affine_cached_ref(table.entries(), digit);

            assert!(actual.y_plus_x.equals(&expected.y_plus_x));
            assert!(actual.y_minus_x.equals(&expected.y_minus_x));
            assert!(actual.t2d.equals(&expected.t2d));
        }
    }

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
