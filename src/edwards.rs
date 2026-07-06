use crate::field::Fe51;

#[cfg(test)]
const BASEPOINT_COMPRESSED: [u8; 32] = [
    0x58, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
];

const BASEPOINT_X_LIMBS: [u64; 5] = [
    1_738_742_601_995_546,
    1_146_398_526_822_698,
    2_070_867_633_025_821,
    562_264_141_797_630,
    587_772_402_128_613,
];
const BASEPOINT_Y_LIMBS: [u64; 5] = [
    1_801_439_850_948_184,
    1_351_079_888_211_148,
    450_359_962_737_049,
    900_719_925_474_099,
    1_801_439_850_948_198,
];
const BASEPOINT_T_LIMBS: [u64; 5] = [
    1_841_354_044_333_475,
    16_398_895_984_059,
    755_974_180_946_558,
    900_171_276_175_154,
    1_821_297_809_914_039,
];

#[derive(Clone, Debug)]
pub(crate) struct EdwardsPoint {
    x: Fe51,
    y: Fe51,
    z: Fe51,
    t: Fe51,
}

// Both tables store `[-N*P, ..., -1*P, identity, 1*P, ..., N*P]` as one
// signed-indexed array (digit `d` at index `d + N`) instead of separate
// positive/negative/identity arrays selected by branching on `d`'s sign: a
// windowed scalar multiply looks up a data-random digit per table per
// iteration, so a sign branch there is unpredictable and measurably costs
// branch mispredicts on the multiscalar hot path.
#[derive(Clone, Debug)]
pub(crate) struct PointTable {
    entries: [CachedPoint; 17],
}

#[derive(Clone, Debug)]
pub(crate) struct BasepointTable {
    entries: [CachedPoint; 2 * BASEPOINT_TABLE_SIZE + 1],
}

// The base-point multiscalar combines two adjacent signed radix-16 digits (each
// in [-8, 8]) into one radix-256 digit `even + (odd << 4)`, whose magnitude is at
// most `8 + 8*16 = 136` (see `base_pair_digit` in wide.rs). The table therefore
// holds multiples `1*B ..= 136*B` (negatives handled separately), so this size
// must equal that maximum digit magnitude.
const BASEPOINT_TABLE_SIZE: usize = 136;

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

impl PointTable {
    pub(crate) fn from_cached(
        cached_points: [CachedPoint; 8],
        negative_cached_points: [CachedPoint; 8],
        identity_cached: CachedPoint,
    ) -> Self {
        let entries = core::array::from_fn(|i| {
            if i < 8 {
                negative_cached_points[7 - i].clone()
            } else if i == 8 {
                identity_cached.clone()
            } else {
                cached_points[i - 9].clone()
            }
        });
        Self { entries }
    }

    pub(crate) fn new(point: &EdwardsPoint) -> Self {
        let points = multiples_of(point);
        let cached_points: [CachedPoint; 8] =
            core::array::from_fn(|i| CachedPoint::new(&points[i]));
        let negative_cached_points = core::array::from_fn(|i| cached_points[i].negate());
        let identity_cached = CachedPoint::new(&EdwardsPoint::identity());
        Self::from_cached(cached_points, negative_cached_points, identity_cached)
    }

    /// Select the cached point for a signed digit in `-8..=8`.
    pub(crate) fn select_signed_cached_ref(&self, digit: i8) -> &CachedPoint {
        debug_assert!((-8..=8).contains(&digit));
        &self.entries[(digit + 8) as usize]
    }
}

impl BasepointTable {
    pub(crate) fn new() -> Self {
        // Built once per process (see BASE_TABLE in verifier.rs), so there's
        // no reason to special-case even m via double() to save a handful of
        // multiplies: this whole computation runs once ever.
        let basepoint = EdwardsPoint::basepoint();
        let mut points = Vec::with_capacity(BASEPOINT_TABLE_SIZE);
        points.push(basepoint.clone());
        for _ in 2..=BASEPOINT_TABLE_SIZE {
            points.push(points.last().unwrap().add(&basepoint));
        }
        let cached_points: [CachedPoint; BASEPOINT_TABLE_SIZE] =
            core::array::from_fn(|i| CachedPoint::new(&points[i]));
        let negative_cached_points: [CachedPoint; BASEPOINT_TABLE_SIZE] =
            core::array::from_fn(|i| cached_points[i].negate());
        let identity_cached = CachedPoint::new(&EdwardsPoint::identity());
        let entries = core::array::from_fn(|i| {
            if i < BASEPOINT_TABLE_SIZE {
                negative_cached_points[BASEPOINT_TABLE_SIZE - 1 - i].clone()
            } else if i == BASEPOINT_TABLE_SIZE {
                identity_cached.clone()
            } else {
                cached_points[i - BASEPOINT_TABLE_SIZE - 1].clone()
            }
        });
        Self { entries }
    }

    /// Select the cached point for a signed digit in
    /// `-BASEPOINT_TABLE_SIZE..=BASEPOINT_TABLE_SIZE`.
    pub(crate) fn select_signed_cached_ref(&self, digit: i16) -> &CachedPoint {
        debug_assert!((-(BASEPOINT_TABLE_SIZE as i16)..=(BASEPOINT_TABLE_SIZE as i16)).contains(&digit));
        &self.entries[(digit + BASEPOINT_TABLE_SIZE as i16) as usize]
    }
}

impl EdwardsPoint {
    #[cfg(test)]
    pub(crate) fn coords(&self) -> (&Fe51, &Fe51, &Fe51, &Fe51) {
        (&self.x, &self.y, &self.z, &self.t)
    }

    #[cfg(test)]
    pub(crate) fn from_coords_unchecked(x: Fe51, y: Fe51, z: Fe51, t: Fe51) -> Self {
        Self { x, y, z, t }
    }

    pub(crate) fn identity() -> Self {
        Self {
            x: Fe51::zero(),
            y: Fe51::one(),
            z: Fe51::one(),
            t: Fe51::zero(),
        }
    }

    pub(crate) fn basepoint() -> Self {
        Self {
            x: Fe51::from_limbs(BASEPOINT_X_LIMBS),
            y: Fe51::from_limbs(BASEPOINT_Y_LIMBS),
            z: Fe51::one(),
            t: Fe51::from_limbs(BASEPOINT_T_LIMBS),
        }
    }

    pub(crate) fn decompress(bytes: &[u8; 32]) -> Option<Self> {
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
    pub(crate) fn compress(&self) -> [u8; 32] {
        let zinv = self.z.invert();
        let x = self.x.multiply(&zinv);
        let y = self.y.multiply(&zinv);
        let mut bytes = y.to_bytes();
        bytes[31] |= (x.is_odd() as u8) << 7;
        bytes
    }
}

fn multiples_of(point: &EdwardsPoint) -> [EdwardsPoint; 8] {
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
    fn precomputed_basepoint_matches_decompression() {
        let decompressed =
            EdwardsPoint::decompress(&BASEPOINT_COMPRESSED).expect("basepoint is valid");
        let precomputed = EdwardsPoint::basepoint();
        assert!(precomputed.x.equals(&decompressed.x));
        assert!(precomputed.y.equals(&decompressed.y));
        assert!(precomputed.z.equals(&decompressed.z));
        assert!(precomputed.t.equals(&decompressed.t));
    }
}
