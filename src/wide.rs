pub(crate) mod avx512ifma {
    use crate::batch::PreparedBatch;
    #[cfg(test)]
    use crate::edwards::EdwardsPoint;
    use crate::edwards::{BasepointTable, CachedPoint, PointTable};
    use crate::field::Fe51;
    use crate::scalar::Radix16;
    use std::arch::x86_64::*;

    const LANES: usize = crate::batch::SIMD_LANES;
    // `__mmask8` and the raw 512-bit loadu/storeu intrinsics throughout this
    // module hard-code 8 lanes; this catches a `SIMD_LANES` change at compile
    // time instead of silently corrupting or truncating lanes at runtime.
    const _: () = assert!(LANES == 8, "avx512ifma assumes exactly 8 SIMD lanes");
    const LIMB_MASK: u64 = (1u64 << 51) - 1;
    #[cfg(test)]
    const FIELD_P_LIMBS: [u64; 5] = [LIMB_MASK - 18, LIMB_MASK, LIMB_MASK, LIMB_MASK, LIMB_MASK];

    pub(crate) struct WideRPoints(WidePoint);

    impl WideRPoints {
        /// Decompression accepts "negative zero" encodings where the sign bit
        /// is set for an `x == 0` point. Dalek rejects those encodings, so the
        /// verifier checks these lanes in addition to canonical `y` bytes.
        pub(crate) fn x_zero_lanes(&self) -> [bool; LANES] {
            self.0.x.is_zero_lanes()
        }
    }

    /// Decompress one SIMD chunk of `R` points and return a per-lane validity mask.
    pub(crate) fn decompress_r_points(r_bytes: &[[u8; 32]; LANES]) -> (WideRPoints, u8) {
        let (point, mask) = decompress_points_wide(r_bytes);
        (WideRPoints(point), mask)
    }

    /// Decode public keys and `R` points together, interleaving the
    /// two inverse-square-root chains (the latency-bound part of decompression).
    /// Returns the key tables + validity and the decompressed `R` + validity.
    pub(crate) fn decode_keys_and_decompress_r(
        keys: &[[u8; 32]; LANES],
        r_bytes: &[[u8; 32]; LANES],
    ) -> ([PointTable; LANES], u8, WideRPoints, u8) {
        let ((kp, kmask), (rp, rmask)) = decompress_point_batches_wide(keys, r_bytes);
        (build_tables_from_point(kp), kmask, WideRPoints(rp), rmask)
    }

    /// Build the per-lane radix-16 cached tables from an already-decompressed
    /// SIMD point.
    fn build_tables_from_point(p: WidePoint) -> [PointTable; LANES] {
        // Tree-balanced multiples (P..8P): critical path ~4 deep instead of the
        // serial 7, with independent adds at each level to expose ILP.
        let p2 = p.add(&p);
        let p4 = p2.add(&p2);
        let p3 = p2.add(&p);
        let mult = [
            p,
            p2,
            p3,
            p4,
            p4.add(&p),  // 5P
            p3.add(&p3), // 6P
            p4.add(&p3), // 7P
            p4.add(&p4), // 8P
        ];

        let two_d = WideFe::two_d();
        type LaneFields = [Fe51; LANES];
        let fields: [(LaneFields, LaneFields, LaneFields, LaneFields, LaneFields); LANES] =
            core::array::from_fn(|i| {
                let m = &mult[i];
                let ypx = m.y.add(&m.x);
                let ymx = m.y.subtract(&m.x);
                let z2 = m.z.double();
                let t2d = m.t.multiply(&two_d);
                let neg_t2d = t2d.negate();
                // These strict values may be stored as loose fields; table
                // consumers tolerate `< 2^52` limbs.
                (
                    ypx.to_fields_loose(),
                    ymx.to_fields_loose(),
                    z2.to_fields_loose(),
                    t2d.to_fields_loose(),
                    neg_t2d.to_fields_loose(),
                )
            });

        let identity = CachedPoint::identity();
        core::array::from_fn(|k| {
            let cached = core::array::from_fn(|i| {
                let (ypx, ymx, z2, t2d, _) = &fields[i];
                CachedPoint::from_fields(ypx[k], ymx[k], z2[k], t2d[k])
            });
            // -P's cached fields are P's with y±x swapped and t2d negated.
            let negative = core::array::from_fn(|i| {
                let (ypx, ymx, z2, _, neg_t2d) = &fields[i];
                CachedPoint::from_fields(ymx[k], ypx[k], z2[k], neg_t2d[k])
            });
            PointTable::from_cached(cached, negative, identity.clone())
        })
    }

    // ZIP-215 cofactored verification: [8](sB - kA - R) == identity.
    pub(crate) fn verify_prepared_zip215(
        prepared: &PreparedBatch<'_>,
        r: &WideRPoints,
        base_table: &BasepointTable,
    ) -> [bool; LANES] {
        let combined = mul_base_minus_public(base_table, prepared);
        let mut check = combined.subtract(&r.0);
        check = check
            .double_without_t()
            .double_without_t()
            .double_without_t();
        check.identity_lanes()
    }

    pub(crate) fn verify_prepared_dalek(
        prepared: &PreparedBatch<'_>,
        r_bytes: &[[u8; 32]; LANES],
        base_table: &BasepointTable,
    ) -> [bool; LANES] {
        let combined = mul_base_minus_public(base_table, prepared);
        let recomputed = combined.compress();
        core::array::from_fn(|lane| recomputed[lane] == r_bytes[lane])
    }

    pub(crate) fn verify_prepared_dalek_projective(
        prepared: &PreparedBatch<'_>,
        r: &WideRPoints,
        base_table: &BasepointTable,
    ) -> [bool; LANES] {
        let combined = mul_base_minus_public(base_table, prepared);
        combined.equals_affine_lanes(&r.0)
    }

    /// Decompression state before the inverse-square-root exponentiation.
    struct DecompressSetup {
        u: WideFe,
        v: WideFe,
        base: WideFe, // u * v^3
        exp: WideFe,  // u * v^7  (raised to (p-5)/8)
        y: WideFe,
        x_signs: [bool; LANES],
    }

    fn decompress_setup(bytes: &[[u8; 32]; LANES]) -> DecompressSetup {
        let mut y_fields = core::array::from_fn(|_| Fe51::zero());
        let mut x_signs = [false; LANES];

        let mut lane = 0;
        while lane < LANES {
            x_signs[lane] = (bytes[lane][31] >> 7) != 0;
            let mut y_bytes = bytes[lane];
            y_bytes[31] &= 0x7f;
            // ZIP-215/Dalek decoding treats y modulo p.
            y_fields[lane] = Fe51::from_bytes_unchecked(&y_bytes);
            lane += 1;
        }

        let y = WideFe::from_fields(&y_fields);
        let yy = y.square();
        let u = yy.subtract(&WideFe::one());
        let v = WideFe::one().add(&WideFe::d().multiply(&yy));
        let v2 = v.square();
        let v3 = v2.multiply(&v);
        let v7 = v3.square().multiply(&v);
        let base = u.multiply(&v3);
        let exp = u.multiply(&v7);
        DecompressSetup {
            u,
            v,
            base,
            exp,
            y,
            x_signs,
        }
    }

    fn decompress_finish(s: DecompressSetup, pow: WideFe) -> (WidePoint, u8) {
        let mut x = s.base.multiply(&pow);

        let vx2 = s.v.multiply(&x.square());
        let first_ok = vx2.equals_lanes(&s.u);

        let x_alt = x.multiply(&WideFe::sqrt_m1());
        let vx_alt2 = s.v.multiply(&x_alt.square());
        let second_ok = vx_alt2.equals_lanes(&s.u);

        let mut alt_mask = 0u8;
        let mut valid_mask = 0u8;
        let mut lane = 0;
        while lane < LANES {
            if first_ok[lane] {
                valid_mask |= 1 << lane;
            } else if second_ok[lane] {
                alt_mask |= 1 << lane;
                valid_mask |= 1 << lane;
            }
            lane += 1;
        }

        x = x.blend(alt_mask, &x_alt);

        // The point built for invalid lanes (not in `valid_mask`) is garbage;
        // callers must gate on `valid_mask`.
        let x_odd = x.is_odd_lanes();
        let x_neg = x.negate();
        let mut negate_mask = 0u8;
        lane = 0;
        while lane < LANES {
            if x_odd[lane] != s.x_signs[lane] {
                negate_mask |= 1 << lane;
            }
            lane += 1;
        }
        x = x.blend(negate_mask, &x_neg);

        let t = x.multiply(&s.y);
        (
            WidePoint {
                x,
                y: s.y,
                z: WideFe::one(),
                t,
            },
            valid_mask,
        )
    }

    /// Decompress one SIMD chunk of compressed Edwards points with per-lane validity.
    fn decompress_points_wide(bytes: &[[u8; 32]; LANES]) -> (WidePoint, u8) {
        let s = decompress_setup(bytes);
        let pow = s.exp.pow_p_minus_5_over_8();
        decompress_finish(s, pow)
    }

    /// Decompress two independent SIMD chunks, interleaving the two
    /// inverse-square-root chains so each fills the other's IFMA latency gaps.
    fn decompress_point_batches_wide(
        a_bytes: &[[u8; 32]; LANES],
        b_bytes: &[[u8; 32]; LANES],
    ) -> ((WidePoint, u8), (WidePoint, u8)) {
        let sa = decompress_setup(a_bytes);
        let sb = decompress_setup(b_bytes);
        let (pa, pb) = WideFe::pow_p_minus_5_over_8_x2(&sa.exp, &sb.exp);
        (decompress_finish(sa, pa), decompress_finish(sb, pb))
    }
    fn mul_base_minus_public(
        base_table: &BasepointTable,
        prepared: &PreparedBatch<'_>,
    ) -> WidePoint {
        let public_key_tables = &prepared.public_key_tables;
        let s_digits = prepared.s_digits;
        let k_digits = prepared.k_digits;

        let mut acc = WidePoint::identity();

        // Start at top digits 63/62; reduced scalars have no digit above 63.
        add_public_digit(&mut acc, public_key_tables, k_digits, 63);
        acc = acc.double4();
        add_base_pair_digit(&mut acc, base_table, s_digits, 31);
        add_public_digit(&mut acc, public_key_tables, k_digits, 62);

        let mut pair = 31;
        while pair > 0 {
            pair -= 1;
            acc = acc.double4();
            add_public_digit(&mut acc, public_key_tables, k_digits, pair * 2 + 1);

            acc = acc.double4();
            add_base_pair_digit(&mut acc, base_table, s_digits, pair);
            add_public_digit(&mut acc, public_key_tables, k_digits, pair * 2);
        }
        acc
    }

    #[inline]
    fn add_base_pair_digit(
        acc: &mut WidePoint,
        base_table: &BasepointTable,
        s_digits: &[Radix16; LANES],
        pair: usize,
    ) {
        let first = base_table.select_signed_cached_ref(base_pair_digit(&s_digits[0], pair));
        let mut selected = [first; LANES];
        let mut lane = 1;
        while lane < LANES {
            selected[lane] =
                base_table.select_signed_cached_ref(base_pair_digit(&s_digits[lane], pair));
            lane += 1;
        }
        let selected = WideCachedPoint::from_cached_refs(&selected);
        acc.add_cached_assign(&selected);
    }

    #[inline]
    fn add_public_digit(
        acc: &mut WidePoint,
        public_key_tables: &[&PointTable; LANES],
        k_digits: &[Radix16; LANES],
        index: usize,
    ) {
        let first = public_key_tables[0].select_signed_cached_ref(-k_digits[0][index]);
        let mut selected = [first; LANES];
        let mut lane = 1;
        while lane < LANES {
            selected[lane] =
                public_key_tables[lane].select_signed_cached_ref(-k_digits[lane][index]);
            lane += 1;
        }
        let selected = WideCachedPoint::from_cached_refs(&selected);
        acc.add_cached_assign(&selected);
    }

    // Fold a radix-16 digit pair into a bounded radix-256 base-table digit.
    #[inline(always)]
    fn base_pair_digit(digits: &Radix16, pair: usize) -> i16 {
        digits[pair * 2] as i16 + ((digits[pair * 2 + 1] as i16) << 4)
    }

    #[derive(Clone, Copy)]
    struct WideFe {
        limbs: [__m512i; 5],
    }

    impl WideFe {
        fn zero() -> Self {
            unsafe {
                let z = _mm512_setzero_si512();
                Self { limbs: [z; 5] }
            }
        }
        fn one() -> Self {
            unsafe {
                let z = _mm512_setzero_si512();
                Self {
                    limbs: [_mm512_set1_epi64(1), z, z, z, z],
                }
            }
        }
        fn from_fields(fields: &[Fe51; LANES]) -> Self {
            let mut by_limb = [[0u64; LANES]; 5];
            let mut lane = 0;
            while lane < LANES {
                let limbs = fields[lane].reduced_limbs();
                let mut limb = 0;
                while limb < 5 {
                    by_limb[limb][lane] = limbs[limb];
                    limb += 1;
                }
                lane += 1;
            }

            Self {
                limbs: [
                    loadu(by_limb[0]),
                    loadu(by_limb[1]),
                    loadu(by_limb[2]),
                    loadu(by_limb[3]),
                    loadu(by_limb[4]),
                ],
            }
        }
        fn from_field_refs(fields: &[&Fe51; LANES]) -> Self {
            let mut by_limb = [[0u64; LANES]; 5];
            let mut lane = 0;
            while lane < LANES {
                let limbs = fields[lane].reduced_limbs();
                let mut limb = 0;
                while limb < 5 {
                    by_limb[limb][lane] = limbs[limb];
                    limb += 1;
                }
                lane += 1;
            }

            Self {
                limbs: [
                    loadu(by_limb[0]),
                    loadu(by_limb[1]),
                    loadu(by_limb[2]),
                    loadu(by_limb[3]),
                    loadu(by_limb[4]),
                ],
            }
        }
        fn to_fields(self) -> [Fe51; LANES] {
            let mut by_limb = [[0u64; LANES]; 5];
            storeu(self.limbs[0], &mut by_limb[0]);
            storeu(self.limbs[1], &mut by_limb[1]);
            storeu(self.limbs[2], &mut by_limb[2]);
            storeu(self.limbs[3], &mut by_limb[3]);
            storeu(self.limbs[4], &mut by_limb[4]);

            core::array::from_fn(|lane| {
                Fe51::from_limbs([
                    by_limb[0][lane],
                    by_limb[1][lane],
                    by_limb[2][lane],
                    by_limb[3][lane],
                    by_limb[4][lane],
                ])
            })
        }

        /// Like `to_fields` but stores loosely-reduced limbs (no canonicalize);
        /// valid because a reduce leaves each limb `< 2^52`.
        fn to_fields_loose(self) -> [Fe51; LANES] {
            let mut by_limb = [[0u64; LANES]; 5];
            storeu(self.limbs[0], &mut by_limb[0]);
            storeu(self.limbs[1], &mut by_limb[1]);
            storeu(self.limbs[2], &mut by_limb[2]);
            storeu(self.limbs[3], &mut by_limb[3]);
            storeu(self.limbs[4], &mut by_limb[4]);

            core::array::from_fn(|lane| {
                Fe51::from_limbs_unchecked([
                    by_limb[0][lane],
                    by_limb[1][lane],
                    by_limb[2][lane],
                    by_limb[3][lane],
                    by_limb[4][lane],
                ])
            })
        }
        // Full reduction keeps results strict enough for small-bias subtracts.
        fn add(&self, rhs: &Self) -> Self {
            unsafe {
                let h = [
                    _mm512_add_epi64(self.limbs[0], rhs.limbs[0]),
                    _mm512_add_epi64(self.limbs[1], rhs.limbs[1]),
                    _mm512_add_epi64(self.limbs[2], rhs.limbs[2]),
                    _mm512_add_epi64(self.limbs[3], rhs.limbs[3]),
                    _mm512_add_epi64(self.limbs[4], rhs.limbs[4]),
                ];
                Self::reduce64(h)
            }
        }
        fn add_loose(&self, rhs: &Self) -> Self {
            unsafe {
                let h = [
                    _mm512_add_epi64(self.limbs[0], rhs.limbs[0]),
                    _mm512_add_epi64(self.limbs[1], rhs.limbs[1]),
                    _mm512_add_epi64(self.limbs[2], rhs.limbs[2]),
                    _mm512_add_epi64(self.limbs[3], rhs.limbs[3]),
                    _mm512_add_epi64(self.limbs[4], rhs.limbs[4]),
                ];
                Self::reduce_loose(h)
            }
        }
        // The 4*p bias is only enough for strict subtrahends (`< 2^52` limbs);
        // loose limb0 can reach < 2^60, so those callers use `subtract_wide`.
        fn subtract(&self, rhs: &Self) -> Self {
            unsafe {
                let bias = [
                    _mm512_set1_epi64(((4 * LIMB_MASK) - 18 * 4) as i64),
                    _mm512_set1_epi64((4 * LIMB_MASK) as i64),
                    _mm512_set1_epi64((4 * LIMB_MASK) as i64),
                    _mm512_set1_epi64((4 * LIMB_MASK) as i64),
                    _mm512_set1_epi64((4 * LIMB_MASK) as i64),
                ];
                let h = [
                    _mm512_sub_epi64(_mm512_add_epi64(self.limbs[0], bias[0]), rhs.limbs[0]),
                    _mm512_sub_epi64(_mm512_add_epi64(self.limbs[1], bias[1]), rhs.limbs[1]),
                    _mm512_sub_epi64(_mm512_add_epi64(self.limbs[2], bias[2]), rhs.limbs[2]),
                    _mm512_sub_epi64(_mm512_add_epi64(self.limbs[3], bias[3]), rhs.limbs[3]),
                    _mm512_sub_epi64(_mm512_add_epi64(self.limbs[4], bias[4]), rhs.limbs[4]),
                ];
                Self::reduce_loose(h)
            }
        }
        // Deferred ops produce loose values: limb0 < 2^60, limbs 1..4 < 2^51.
        // `_wide` subtracts use a 2048*p bias for up to two loose subtrahends.
        // `square`/`square_loose` share accumulation and differ only in reduction.
        fn square_accum(&self) -> ([__m512i; 5], [__m512i; 5]) {
            unsafe {
                let z = _mm512_setzero_si512();
                let mut lo = [z; 5];
                let mut hi = [z; 5];

                // Normalize loose limb0 before squaring; torsion cases can represent
                // zero as p, and doubled IFMA inputs must stay under 52 bits.
                let limbs = {
                    let mask = _mm512_set1_epi64(LIMB_MASK as i64);
                    let mut l = self.limbs;
                    let mut i = 0;
                    while i < 4 {
                        let carry = _mm512_srli_epi64(l[i], 51);
                        l[i] = _mm512_and_si512(l[i], mask);
                        l[i + 1] = _mm512_add_epi64(l[i + 1], carry);
                        i += 1;
                    }
                    l
                };

                let f0_2 = _mm512_add_epi64(limbs[0], limbs[0]);
                let f1_2 = _mm512_add_epi64(limbs[1], limbs[1]);
                let f2_2 = _mm512_add_epi64(limbs[2], limbs[2]);
                let f3_2 = _mm512_add_epi64(limbs[3], limbs[3]);

                madd_one(&mut lo[0], &mut hi[0], limbs[0], limbs[0]);
                let (mut wlo, mut whi) = (z, z);
                madd_one(&mut wlo, &mut whi, f1_2, limbs[4]);
                madd_one(&mut wlo, &mut whi, f2_2, limbs[3]);
                add_wrap19(&mut lo[0], &mut hi[0], wlo, whi);

                madd_one(&mut lo[1], &mut hi[1], f0_2, limbs[1]);
                let (mut wlo, mut whi) = (z, z);
                madd_one(&mut wlo, &mut whi, f2_2, limbs[4]);
                madd_one(&mut wlo, &mut whi, limbs[3], limbs[3]);
                add_wrap19(&mut lo[1], &mut hi[1], wlo, whi);

                madd_one(&mut lo[2], &mut hi[2], f0_2, limbs[2]);
                madd_one(&mut lo[2], &mut hi[2], limbs[1], limbs[1]);
                let (mut wlo, mut whi) = (z, z);
                madd_one(&mut wlo, &mut whi, f3_2, limbs[4]);
                add_wrap19(&mut lo[2], &mut hi[2], wlo, whi);

                madd_one(&mut lo[3], &mut hi[3], f0_2, limbs[3]);
                madd_one(&mut lo[3], &mut hi[3], f1_2, limbs[2]);
                let (mut wlo, mut whi) = (z, z);
                madd_one(&mut wlo, &mut whi, limbs[4], limbs[4]);
                add_wrap19(&mut lo[3], &mut hi[3], wlo, whi);

                madd_one(&mut lo[4], &mut hi[4], f0_2, limbs[4]);
                madd_one(&mut lo[4], &mut hi[4], f1_2, limbs[3]);
                madd_one(&mut lo[4], &mut hi[4], limbs[2], limbs[2]);

                (lo, hi)
            }
        }
        fn square_loose(&self) -> Self {
            let (lo, hi) = self.square_accum();
            Self::reduce_ifma_loose(lo, hi)
        }
        // Shared accumulation for `multiply`/`multiply_loose`: they differ only
        // in which `reduce_ifma*` pass is applied to the raw (lo, hi) columns.
        fn multiply_accum(&self, rhs: &Self) -> ([__m512i; 5], [__m512i; 5]) {
            unsafe {
                let z = _mm512_setzero_si512();
                let mut lo = [z; 5];
                let mut hi = [z; 5];

                madd_one(&mut lo[0], &mut hi[0], self.limbs[0], rhs.limbs[0]);
                let (mut wlo, mut whi) = (z, z);
                madd_one(&mut wlo, &mut whi, self.limbs[1], rhs.limbs[4]);
                madd_one(&mut wlo, &mut whi, self.limbs[2], rhs.limbs[3]);
                madd_one(&mut wlo, &mut whi, self.limbs[3], rhs.limbs[2]);
                madd_one(&mut wlo, &mut whi, self.limbs[4], rhs.limbs[1]);
                add_wrap19(&mut lo[0], &mut hi[0], wlo, whi);

                madd_one(&mut lo[1], &mut hi[1], self.limbs[0], rhs.limbs[1]);
                madd_one(&mut lo[1], &mut hi[1], self.limbs[1], rhs.limbs[0]);
                let (mut wlo, mut whi) = (z, z);
                madd_one(&mut wlo, &mut whi, self.limbs[2], rhs.limbs[4]);
                madd_one(&mut wlo, &mut whi, self.limbs[3], rhs.limbs[3]);
                madd_one(&mut wlo, &mut whi, self.limbs[4], rhs.limbs[2]);
                add_wrap19(&mut lo[1], &mut hi[1], wlo, whi);

                madd_one(&mut lo[2], &mut hi[2], self.limbs[0], rhs.limbs[2]);
                madd_one(&mut lo[2], &mut hi[2], self.limbs[1], rhs.limbs[1]);
                madd_one(&mut lo[2], &mut hi[2], self.limbs[2], rhs.limbs[0]);
                let (mut wlo, mut whi) = (z, z);
                madd_one(&mut wlo, &mut whi, self.limbs[3], rhs.limbs[4]);
                madd_one(&mut wlo, &mut whi, self.limbs[4], rhs.limbs[3]);
                add_wrap19(&mut lo[2], &mut hi[2], wlo, whi);

                madd_one(&mut lo[3], &mut hi[3], self.limbs[0], rhs.limbs[3]);
                madd_one(&mut lo[3], &mut hi[3], self.limbs[1], rhs.limbs[2]);
                madd_one(&mut lo[3], &mut hi[3], self.limbs[2], rhs.limbs[1]);
                madd_one(&mut lo[3], &mut hi[3], self.limbs[3], rhs.limbs[0]);
                let (mut wlo, mut whi) = (z, z);
                madd_one(&mut wlo, &mut whi, self.limbs[4], rhs.limbs[4]);
                add_wrap19(&mut lo[3], &mut hi[3], wlo, whi);

                madd_one(&mut lo[4], &mut hi[4], self.limbs[0], rhs.limbs[4]);
                madd_one(&mut lo[4], &mut hi[4], self.limbs[1], rhs.limbs[3]);
                madd_one(&mut lo[4], &mut hi[4], self.limbs[2], rhs.limbs[2]);
                madd_one(&mut lo[4], &mut hi[4], self.limbs[3], rhs.limbs[1]);
                madd_one(&mut lo[4], &mut hi[4], self.limbs[4], rhs.limbs[0]);

                (lo, hi)
            }
        }
        fn multiply_loose(&self, rhs: &Self) -> Self {
            let (lo, hi) = self.multiply_accum(rhs);
            Self::reduce_ifma_loose(lo, hi)
        }

        // `reduce_ifma` without the trailing `reduce_loose` pass: one IFMA carry
        // pass only. Leaves limb0 < 2^60, limbs 1..4 < 2^51.
        fn reduce_ifma_loose(mut lo: [__m512i; 5], hi: [__m512i; 5]) -> Self {
            unsafe {
                let mask = _mm512_set1_epi64(LIMB_MASK as i64);
                let nineteen = _mm512_set1_epi64(19);

                let mut i = 0;
                while i < 4 {
                    let carry =
                        _mm512_add_epi64(_mm512_srli_epi64(lo[i], 51), _mm512_slli_epi64(hi[i], 1));
                    lo[i] = _mm512_and_si512(lo[i], mask);
                    lo[i + 1] = _mm512_add_epi64(lo[i + 1], carry);
                    i += 1;
                }

                let carry =
                    _mm512_add_epi64(_mm512_srli_epi64(lo[4], 51), _mm512_slli_epi64(hi[4], 1));
                lo[4] = _mm512_and_si512(lo[4], mask);
                lo[0] = _mm512_add_epi64(lo[0], _mm512_mullo_epi64(carry, nineteen));

                Self { limbs: lo }
            }
        }

        // `self + 2048*p - rhs`, with `self`/`rhs` possibly loose (limb0 < 2^60).
        fn subtract_wide(&self, rhs: &Self) -> Self {
            unsafe {
                let b0 = _mm512_set1_epi64((2048 * (LIMB_MASK - 18)) as i64);
                let bn = _mm512_set1_epi64((2048 * LIMB_MASK) as i64);
                let h = [
                    _mm512_sub_epi64(_mm512_add_epi64(self.limbs[0], b0), rhs.limbs[0]),
                    _mm512_sub_epi64(_mm512_add_epi64(self.limbs[1], bn), rhs.limbs[1]),
                    _mm512_sub_epi64(_mm512_add_epi64(self.limbs[2], bn), rhs.limbs[2]),
                    _mm512_sub_epi64(_mm512_add_epi64(self.limbs[3], bn), rhs.limbs[3]),
                    _mm512_sub_epi64(_mm512_add_epi64(self.limbs[4], bn), rhs.limbs[4]),
                ];
                Self::reduce_loose(h)
            }
        }

        // `self + 2048*p - lhs - rhs`, with all three possibly loose.
        fn subtract_sum_wide(&self, lhs: &Self, rhs: &Self) -> Self {
            unsafe {
                let b0 = _mm512_set1_epi64((2048 * (LIMB_MASK - 18)) as i64);
                let bn = _mm512_set1_epi64((2048 * LIMB_MASK) as i64);
                let bias = [b0, bn, bn, bn, bn];
                let h = core::array::from_fn(|i| {
                    _mm512_sub_epi64(
                        _mm512_sub_epi64(_mm512_add_epi64(self.limbs[i], bias[i]), lhs.limbs[i]),
                        rhs.limbs[i],
                    )
                });
                Self::reduce_loose(h)
            }
        }

        // `2048*p - lhs - rhs`, with `lhs`/`rhs` possibly loose.
        fn negate_sum_wide(lhs: &Self, rhs: &Self) -> Self {
            unsafe {
                let b0 = _mm512_set1_epi64((2048 * (LIMB_MASK - 18)) as i64);
                let bn = _mm512_set1_epi64((2048 * LIMB_MASK) as i64);
                let bias = [b0, bn, bn, bn, bn];
                let h = core::array::from_fn(|i| {
                    _mm512_sub_epi64(_mm512_sub_epi64(bias[i], lhs.limbs[i]), rhs.limbs[i])
                });
                Self::reduce_loose(h)
            }
        }
        fn negate(&self) -> Self {
            Self::zero().subtract(self)
        }
        fn double(&self) -> Self {
            self.add(self)
        }
        fn double_loose(&self) -> Self {
            self.add_loose(self)
        }
        fn square(&self) -> Self {
            let (lo, hi) = self.square_accum();
            Self::reduce_ifma(lo, hi)
        }
        fn multiply(&self, rhs: &Self) -> Self {
            let (lo, hi) = self.multiply_accum(rhs);
            Self::reduce_ifma(lo, hi)
        }
        fn pow_p_minus_5_over_8(&self) -> Self {
            let t0 = self.square();
            let t1 = t0.square_repeat::<2>().multiply(self);
            let t0 = t0.multiply(&t1);
            let t0 = t0.square().multiply(&t1);
            let t1 = t0.square_repeat::<5>();
            let t0 = t1.multiply(&t0);
            let t1 = t0.square_repeat::<10>().multiply(&t0);
            let t2 = t1.square_repeat::<20>();
            let t1 = t2.multiply(&t1);
            let t1 = t1.square_repeat::<10>();
            let t0 = t1.multiply(&t0);
            let t1 = t0.square_repeat::<50>().multiply(&t0);
            let t2 = t1.square_repeat::<100>();
            let t1 = t2.multiply(&t1);
            let t1 = t1.square_repeat::<50>();
            let t0 = t1.multiply(&t0);
            t0.square_repeat::<2>().multiply(self)
        }

        fn invert(&self) -> Self {
            let z = self;
            let t0 = z.square();
            let t1 = t0.square_repeat::<2>().multiply(z);
            let z11 = t0.multiply(&t1);
            let a = z11.square().multiply(&t1);
            let b = a.square_repeat::<5>().multiply(&a);
            let c = b.square_repeat::<10>().multiply(&b);
            let d = c.square_repeat::<20>().multiply(&c);
            let e = d.square_repeat::<10>().multiply(&b);
            let f = e.square_repeat::<50>().multiply(&e);
            let g = f.square_repeat::<100>().multiply(&f);
            let h = g.square_repeat::<50>().multiply(&e);
            h.square_repeat::<5>().multiply(&z11)
        }
        // Intermediate squarings stay loose; the final result is strict because
        // callers feed it to `multiply`, which requires `< 2^52` inputs.
        fn square_repeat<const N: usize>(&self) -> Self {
            let mut out = *self;
            let mut i = 0;
            while i < N {
                out = if i + 1 < N {
                    out.square_loose()
                } else {
                    out.square()
                };
                i += 1;
            }
            out
        }

        // Interleave two exponentiation chains to hide IFMA latency.
        fn square_repeat_x2<const N: usize>(a: &Self, b: &Self) -> (Self, Self) {
            let (mut x, mut y) = (*a, *b);
            let mut i = 0;
            while i < N {
                if i + 1 < N {
                    x = x.square_loose();
                    y = y.square_loose();
                } else {
                    x = x.square();
                    y = y.square();
                }
                i += 1;
            }
            (x, y)
        }

        fn pow_p_minus_5_over_8_x2(a: &Self, b: &Self) -> (Self, Self) {
            let (t0a, t0b) = (a.square(), b.square());
            let (sa, sb) = Self::square_repeat_x2::<2>(&t0a, &t0b);
            let (t1a, t1b) = (sa.multiply(a), sb.multiply(b));
            let (t0a, t0b) = (t0a.multiply(&t1a), t0b.multiply(&t1b));
            let (qa, qb) = (t0a.square(), t0b.square());
            let (t0a, t0b) = (qa.multiply(&t1a), qb.multiply(&t1b));
            let (t1a, t1b) = Self::square_repeat_x2::<5>(&t0a, &t0b);
            let (t0a, t0b) = (t1a.multiply(&t0a), t1b.multiply(&t0b));
            let (ra, rb) = Self::square_repeat_x2::<10>(&t0a, &t0b);
            let (t1a, t1b) = (ra.multiply(&t0a), rb.multiply(&t0b));
            let (t2a, t2b) = Self::square_repeat_x2::<20>(&t1a, &t1b);
            let (t1a, t1b) = (t2a.multiply(&t1a), t2b.multiply(&t1b));
            let (t1a, t1b) = Self::square_repeat_x2::<10>(&t1a, &t1b);
            let (t0a, t0b) = (t1a.multiply(&t0a), t1b.multiply(&t0b));
            let (ra, rb) = Self::square_repeat_x2::<50>(&t0a, &t0b);
            let (t1a, t1b) = (ra.multiply(&t0a), rb.multiply(&t0b));
            let (t2a, t2b) = Self::square_repeat_x2::<100>(&t1a, &t1b);
            let (t1a, t1b) = (t2a.multiply(&t1a), t2b.multiply(&t1b));
            let (t1a, t1b) = Self::square_repeat_x2::<50>(&t1a, &t1b);
            let (t0a, t0b) = (t1a.multiply(&t0a), t1b.multiply(&t0b));
            let (fa, fb) = Self::square_repeat_x2::<2>(&t0a, &t0b);
            (fa.multiply(a), fb.multiply(b))
        }
        fn equals_lanes(self, rhs: &Self) -> [bool; LANES] {
            self.subtract(rhs).is_zero_lanes()
        }
        fn is_zero_lanes(self) -> [bool; LANES] {
            unsafe {
                let c = self.canonical();
                let zero = _mm512_setzero_si512();
                let mask = _mm512_cmpeq_epu64_mask(c.limbs[0], zero)
                    & _mm512_cmpeq_epu64_mask(c.limbs[1], zero)
                    & _mm512_cmpeq_epu64_mask(c.limbs[2], zero)
                    & _mm512_cmpeq_epu64_mask(c.limbs[3], zero)
                    & _mm512_cmpeq_epu64_mask(c.limbs[4], zero);
                mask_to_lanes(mask)
            }
        }
        fn is_odd_lanes(self) -> [bool; LANES] {
            unsafe {
                let c = self.canonical();
                let one = _mm512_set1_epi64(1);
                mask_to_lanes(_mm512_test_epi64_mask(c.limbs[0], one))
            }
        }
        /// Vectorized `Fe51::canonical` for all lanes. `reduce64` bounds limbs
        /// 1..4, making `>= p` an exact high-limb check plus limb0 threshold.
        fn canonical(&self) -> Self {
            unsafe {
                let reduced = Self::reduce64(self.limbs);
                let mask = _mm512_set1_epi64(LIMB_MASK as i64);
                let p0 = _mm512_set1_epi64((LIMB_MASK - 18) as i64);

                let ge_high = _mm512_cmpeq_epu64_mask(reduced.limbs[1], mask)
                    & _mm512_cmpeq_epu64_mask(reduced.limbs[2], mask)
                    & _mm512_cmpeq_epu64_mask(reduced.limbs[3], mask)
                    & _mm512_cmpeq_epu64_mask(reduced.limbs[4], mask);
                let ge_p = ge_high & _mm512_cmpge_epu64_mask(reduced.limbs[0], p0);

                let zero = _mm512_setzero_si512();
                let sub0 = _mm512_sub_epi64(reduced.limbs[0], p0);
                Self {
                    limbs: [
                        _mm512_mask_blend_epi64(ge_p, reduced.limbs[0], sub0),
                        _mm512_mask_blend_epi64(ge_p, reduced.limbs[1], zero),
                        _mm512_mask_blend_epi64(ge_p, reduced.limbs[2], zero),
                        _mm512_mask_blend_epi64(ge_p, reduced.limbs[3], zero),
                        _mm512_mask_blend_epi64(ge_p, reduced.limbs[4], zero),
                    ],
                }
            }
        }
        fn blend(&self, mask: u8, rhs: &Self) -> Self {
            unsafe {
                let mask = mask as __mmask8;
                Self {
                    limbs: [
                        _mm512_mask_blend_epi64(mask, self.limbs[0], rhs.limbs[0]),
                        _mm512_mask_blend_epi64(mask, self.limbs[1], rhs.limbs[1]),
                        _mm512_mask_blend_epi64(mask, self.limbs[2], rhs.limbs[2]),
                        _mm512_mask_blend_epi64(mask, self.limbs[3], rhs.limbs[3]),
                        _mm512_mask_blend_epi64(mask, self.limbs[4], rhs.limbs[4]),
                    ],
                }
            }
        }
        fn reduce_ifma(mut lo: [__m512i; 5], hi: [__m512i; 5]) -> Self {
            unsafe {
                let mask = _mm512_set1_epi64(LIMB_MASK as i64);
                let nineteen = _mm512_set1_epi64(19);

                let mut i = 0;
                while i < 4 {
                    let carry =
                        _mm512_add_epi64(_mm512_srli_epi64(lo[i], 51), _mm512_slli_epi64(hi[i], 1));
                    lo[i] = _mm512_and_si512(lo[i], mask);
                    lo[i + 1] = _mm512_add_epi64(lo[i + 1], carry);
                    i += 1;
                }

                let carry =
                    _mm512_add_epi64(_mm512_srli_epi64(lo[4], 51), _mm512_slli_epi64(hi[4], 1));
                lo[4] = _mm512_and_si512(lo[4], mask);
                lo[0] = _mm512_add_epi64(lo[0], _mm512_mullo_epi64(carry, nineteen));

                // One extra carry pass leaves `< 2^52` limbs, enough for
                // multiply/square consumers.
                Self::reduce_loose(lo)
            }
        }
        /// One carry pass: limbs 1..4 become `< 2^51`; limb 0 may keep the
        /// small wraparound residual needed by additive consumers.
        fn reduce_loose(mut h: [__m512i; 5]) -> Self {
            unsafe {
                let mask = _mm512_set1_epi64(LIMB_MASK as i64);
                let nineteen = _mm512_set1_epi64(19);

                let mut i = 0;
                while i < 4 {
                    let carry = _mm512_srli_epi64(h[i], 51);
                    h[i] = _mm512_and_si512(h[i], mask);
                    h[i + 1] = _mm512_add_epi64(h[i + 1], carry);
                    i += 1;
                }

                let carry = _mm512_srli_epi64(h[4], 51);
                h[4] = _mm512_and_si512(h[4], mask);
                h[0] = _mm512_add_epi64(h[0], _mm512_mullo_epi64(carry, nineteen));

                Self { limbs: h }
            }
        }
        /// Two carry passes, used when `add`/`canonical` need near-strict limbs.
        fn reduce64(mut h: [__m512i; 5]) -> Self {
            unsafe {
                let mask = _mm512_set1_epi64(LIMB_MASK as i64);
                let nineteen = _mm512_set1_epi64(19);

                let mut pass = 0;
                while pass < 2 {
                    let mut i = 0;
                    while i < 4 {
                        let carry = _mm512_srli_epi64(h[i], 51);
                        h[i] = _mm512_and_si512(h[i], mask);
                        h[i + 1] = _mm512_add_epi64(h[i + 1], carry);
                        i += 1;
                    }

                    let carry = _mm512_srli_epi64(h[4], 51);
                    h[4] = _mm512_and_si512(h[4], mask);
                    h[0] = _mm512_add_epi64(h[0], _mm512_mullo_epi64(carry, nineteen));
                    pass += 1;
                }

                Self { limbs: h }
            }
        }
    }

    #[derive(Clone, Copy)]
    struct WidePoint {
        x: WideFe,
        y: WideFe,
        z: WideFe,
        t: WideFe,
    }

    #[derive(Clone, Copy)]
    struct WideCachedPoint {
        y_plus_x: WideFe,
        y_minus_x: WideFe,
        z2: WideFe,
        t2d: WideFe,
    }

    impl WideCachedPoint {
        fn from_cached_refs(points: &[&CachedPoint; LANES]) -> Self {
            let y_plus_x = core::array::from_fn(|lane| points[lane].coords().0);
            let y_minus_x = core::array::from_fn(|lane| points[lane].coords().1);
            let z2 = core::array::from_fn(|lane| points[lane].coords().2);
            let t2d = core::array::from_fn(|lane| points[lane].coords().3);
            Self {
                y_plus_x: WideFe::from_field_refs(&y_plus_x),
                y_minus_x: WideFe::from_field_refs(&y_minus_x),
                z2: WideFe::from_field_refs(&z2),
                t2d: WideFe::from_field_refs(&t2d),
            }
        }
    }

    impl WidePoint {
        fn identity() -> Self {
            Self {
                x: WideFe::zero(),
                y: WideFe::one(),
                z: WideFe::one(),
                t: WideFe::zero(),
            }
        }
        fn compress(&self) -> [[u8; 32]; LANES] {
            let zinv = self.z.invert();
            let x = self.x.multiply(&zinv);
            let y = self.y.multiply(&zinv);
            let xs = x.to_fields();
            let ys = y.to_fields();
            core::array::from_fn(|lane| {
                let mut bytes = ys[lane].to_bytes();
                bytes[31] |= (xs[lane].is_odd() as u8) << 7;
                bytes
            })
        }
        fn equals_affine_lanes(&self, affine: &Self) -> [bool; LANES] {
            let x = affine.x.multiply(&self.z);
            let y = affine.y.multiply(&self.z);
            let x_equal = self.x.equals_lanes(&x);
            let y_equal = self.y.equals_lanes(&y);
            core::array::from_fn(|lane| x_equal[lane] && y_equal[lane])
        }
        // Table-building points are strict, so small-bias `subtract` is valid.
        // The hot path uses `add_cached_assign` for loose intermediates.
        fn add(&self, rhs: &Self) -> Self {
            let a = self.y.subtract(&self.x).multiply(&rhs.y.subtract(&rhs.x));
            let b = self.y.add_loose(&self.x).multiply(&rhs.y.add_loose(&rhs.x));
            let c = self.t.multiply(&rhs.t).multiply(&WideFe::two_d());
            let d = self.z.multiply(&rhs.z).double_loose();
            let e = b.subtract(&a);
            let f = d.subtract(&c);
            let g = d.add_loose(&c);
            let h = b.add_loose(&a);

            Self {
                x: e.multiply(&f),
                y: g.multiply(&h),
                t: e.multiply(&h),
                z: f.multiply(&g),
            }
        }
        fn add_cached_assign(&mut self, rhs: &WideCachedPoint) {
            // Loose products feed additive ops; use wide subtracts for limb0
            // values up to ~2^60.
            let a = self.y.subtract(&self.x).multiply_loose(&rhs.y_minus_x);
            let b = self.y.add_loose(&self.x).multiply_loose(&rhs.y_plus_x);
            let e = b.subtract_wide(&a);
            let h = b.add_loose(&a);
            let c = self.t.multiply_loose(&rhs.t2d);
            let d = self.z.multiply_loose(&rhs.z2);
            let f = d.subtract_wide(&c);
            let g = d.add_loose(&c);

            self.x = e.multiply(&f);
            self.t = e.multiply(&h);
            self.z = f.multiply(&g);
            self.y = g.multiply(&h);
        }
        fn subtract(&self, rhs: &Self) -> Self {
            self.add(&rhs.negate())
        }
        fn negate(&self) -> Self {
            Self {
                x: self.x.negate(),
                y: self.y,
                z: self.z,
                t: self.t.negate(),
            }
        }
        fn double(&self) -> Self {
            self.double_impl::<true>()
        }
        fn double_without_t(&self) -> Self {
            self.double_impl::<false>()
        }

        #[inline(never)]
        fn double4(&self) -> Self {
            let doubled = self
                .double_without_t()
                .double_without_t()
                .double_without_t();
            doubled.double()
        }
        fn double_impl<const COMPUTE_T: bool>(&self) -> Self {
            // Loose squares feed additive ops; use wide subtract/negate for
            // limb0 values up to ~2^60.
            let a = self.x.square_loose();
            let b = self.y.square_loose();
            let c = self.z.square_loose().double_loose();
            let e = self
                .x
                .add_loose(&self.y)
                .square_loose()
                .subtract_sum_wide(&a, &b);
            let g = b.subtract_wide(&a);
            let f = b.subtract_sum_wide(&a, &c);
            let h = WideFe::negate_sum_wide(&a, &b);
            let t = if COMPUTE_T {
                e.multiply(&h)
            } else {
                WideFe::zero()
            };

            Self {
                x: e.multiply(&f),
                y: g.multiply(&h),
                t,
                z: f.multiply(&g),
            }
        }
        fn identity_lanes(self) -> [bool; LANES] {
            let x_zero = self.x.is_zero_lanes();
            let yz_equal = self.y.equals_lanes(&self.z);
            core::array::from_fn(|lane| x_zero[lane] && yz_equal[lane])
        }

        #[cfg(test)]
        fn from_points(points: &[EdwardsPoint; LANES]) -> Self {
            let xs = core::array::from_fn(|lane| *points[lane].coords().0);
            let ys = core::array::from_fn(|lane| *points[lane].coords().1);
            let zs = core::array::from_fn(|lane| *points[lane].coords().2);
            let ts = core::array::from_fn(|lane| *points[lane].coords().3);
            Self {
                x: WideFe::from_fields(&xs),
                y: WideFe::from_fields(&ys),
                z: WideFe::from_fields(&zs),
                t: WideFe::from_fields(&ts),
            }
        }

        #[cfg(test)]
        fn to_points(self) -> [EdwardsPoint; LANES] {
            let xs = self.x.to_fields();
            let ys = self.y.to_fields();
            let zs = self.z.to_fields();
            let ts = self.t.to_fields();
            core::array::from_fn(|lane| {
                EdwardsPoint::from_coords_unchecked(xs[lane], ys[lane], zs[lane], ts[lane])
            })
        }
    }

    impl WideFe {
        fn constant(limbs: [u64; 5]) -> Self {
            unsafe {
                Self {
                    limbs: [
                        _mm512_set1_epi64(limbs[0] as i64),
                        _mm512_set1_epi64(limbs[1] as i64),
                        _mm512_set1_epi64(limbs[2] as i64),
                        _mm512_set1_epi64(limbs[3] as i64),
                        _mm512_set1_epi64(limbs[4] as i64),
                    ],
                }
            }
        }
        // Curve constants are defined once in `field.rs` and broadcast here, so
        // the scalar and SIMD field paths cannot drift.
        fn d() -> Self {
            Self::constant(crate::field::D_LIMBS)
        }
        fn sqrt_m1() -> Self {
            Self::constant(crate::field::SQRT_M1_LIMBS)
        }
        fn two_d() -> Self {
            Self::constant(crate::field::TWO_D_LIMBS)
        }
    }
    fn madd_one(lo: &mut __m512i, hi: &mut __m512i, a: __m512i, b: __m512i) {
        unsafe {
            *lo = _mm512_madd52lo_epu64(*lo, a, b);
            *hi = _mm512_madd52hi_epu64(*hi, a, b);
        }
    }
    fn add_wrap19(lo: &mut __m512i, hi: &mut __m512i, wrap_lo: __m512i, wrap_hi: __m512i) {
        unsafe {
            let nineteen = _mm512_set1_epi64(19);
            *lo = _mm512_add_epi64(*lo, _mm512_mullo_epi64(wrap_lo, nineteen));
            *hi = _mm512_add_epi64(*hi, _mm512_mullo_epi64(wrap_hi, nineteen));
        }
    }
    fn loadu(values: [u64; LANES]) -> __m512i {
        unsafe { _mm512_loadu_si512(values.as_ptr() as *const __m512i) }
    }
    fn storeu(value: __m512i, out: &mut [u64; LANES]) {
        unsafe { _mm512_storeu_si512(out.as_mut_ptr() as *mut __m512i, value) }
    }
    fn mask_to_lanes(mask: __mmask8) -> [bool; LANES] {
        core::array::from_fn(|lane| (mask & (1 << lane)) != 0)
    }

    /// Scalar reference for `WideFe::canonical`, kept only as a test check for
    /// the vectorized path.
    #[cfg(test)]
    fn canonicalize_field_limbs(limbs: [u64; 5]) -> [u64; 5] {
        // The partial carry chain below relies on limbs already being < 2^52.
        debug_assert!(limbs.iter().all(|&l| l < (1u64 << 52)));
        let mut h = [
            limbs[0] as u128,
            limbs[1] as u128,
            limbs[2] as u128,
            limbs[3] as u128,
            limbs[4] as u128,
        ];

        let mut i = 0;
        while i < 4 {
            let carry = h[i] >> 51;
            h[i] &= LIMB_MASK as u128;
            h[i + 1] += carry;
            i += 1;
        }

        let carry = h[4] >> 51;
        h[4] &= LIMB_MASK as u128;
        h[0] += carry * 19;

        let carry = h[0] >> 51;
        h[0] &= LIMB_MASK as u128;
        h[1] += carry;

        let carry = h[1] >> 51;
        h[1] &= LIMB_MASK as u128;
        h[2] += carry;

        let mut out = [
            h[0] as u64,
            h[1] as u64,
            h[2] as u64,
            h[3] as u64,
            h[4] as u64,
        ];
        if cmp_field_limbs(&out, &FIELD_P_LIMBS) != core::cmp::Ordering::Less {
            sub_field_limbs(&mut out, &FIELD_P_LIMBS);
        }
        out
    }

    #[cfg(test)]
    fn cmp_field_limbs(lhs: &[u64; 5], rhs: &[u64; 5]) -> core::cmp::Ordering {
        let mut i = 5;
        while i > 0 {
            i -= 1;
            match lhs[i].cmp(&rhs[i]) {
                core::cmp::Ordering::Equal => {}
                order => return order,
            }
        }
        core::cmp::Ordering::Equal
    }

    #[cfg(test)]
    fn sub_field_limbs(lhs: &mut [u64; 5], rhs: &[u64; 5]) {
        let mut borrow = 0i128;
        let base = 1i128 << 51;
        let mut i = 0;
        while i < 5 {
            let value = lhs[i] as i128 - rhs[i] as i128 - borrow;
            if value < 0 {
                lhs[i] = (value + base) as u64;
                borrow = 1;
            } else {
                lhs[i] = value as u64;
                borrow = 0;
            }
            i += 1;
        }
    }

    #[cfg(test)]
    mod simd_torsion_tests {
        use super::*;

        fn strict_square_n(x: &WideFe, n: usize) -> WideFe {
            let mut out = *x;
            for _ in 0..n {
                out = out.square();
            }
            out
        }

        fn wide_from_rows(rows: [[u64; LANES]; 5]) -> WideFe {
            WideFe {
                limbs: core::array::from_fn(|i| loadu(rows[i])),
            }
        }

        /// Cross-check vectorized canonical predicates against scalar references.
        fn check_canonical(rows: [[u64; LANES]; 5]) {
            let wide = wide_from_rows(rows);
            let canonical = wide.canonical();
            let mut canonical_rows = [[0u64; LANES]; 5];
            for (limb, row) in canonical_rows.iter_mut().enumerate() {
                storeu(canonical.limbs[limb], row);
            }
            let is_zero = wide.is_zero_lanes();
            let is_odd = wide.is_odd_lanes();

            for lane in 0..LANES {
                let input: [u64; 5] = core::array::from_fn(|limb| rows[limb][lane]);
                let expected = canonicalize_field_limbs(input);
                let actual: [u64; 5] = core::array::from_fn(|limb| canonical_rows[limb][lane]);
                assert_eq!(
                    actual, expected,
                    "lane {lane} diverged from scalar reference"
                );
                assert_eq!(
                    is_zero[lane],
                    expected == [0u64; 5],
                    "is_zero_lanes lane {lane}"
                );
                assert_eq!(
                    is_odd[lane],
                    (expected[0] & 1) != 0,
                    "is_odd_lanes lane {lane}"
                );

                let expected_bytes = crate::field::Fe51::from_limbs(input).to_bytes();
                let actual_bytes = crate::field::Fe51::from_limbs(actual).to_bytes();
                assert_eq!(
                    actual_bytes, expected_bytes,
                    "lane {lane} diverged from field.rs Fe51 reference"
                );
            }
        }

        #[test]
        fn canonical_matches_references_on_boundary_values() {
            let zero = [0u64; 5];
            let p = FIELD_P_LIMBS;
            let p_minus_1 = {
                let mut l = p;
                l[0] -= 1;
                l
            };
            let p_plus_1 = {
                let mut l = p;
                l[0] += 1;
                l
            };
            // Every limb at its documented max input bound (2^52 - 1).
            let max_limbs = [(1u64 << 52) - 1; 5];
            let hand_picked = [zero, p, p_minus_1, p_plus_1, max_limbs];

            let mut state = 0x2545f4914f6cdd1du64;
            let mut next = || {
                state = state
                    .wrapping_mul(0xd1342543de82ef95)
                    .wrapping_add(0x9e3779b97f4a7c15);
                state
            };

            let mut rows = [[0u64; LANES]; 5];
            for lane in 0..LANES {
                let limbs = if lane < hand_picked.len() {
                    hand_picked[lane]
                } else {
                    core::array::from_fn(|_| next() & ((1u64 << 52) - 1))
                };
                for limb in 0..5 {
                    rows[limb][lane] = limbs[limb];
                }
            }
            check_canonical(rows);
        }

        #[test]
        fn canonical_matches_references_on_random_values() {
            let mut state = 0x9e3779b97f4a7c15u64;
            let mut next = || {
                state = state
                    .wrapping_mul(0xd1342543de82ef95)
                    .wrapping_add(0x2545f4914f6cdd1d);
                state
            };

            let mut round = 0;
            while round < 512 {
                let mut rows = [[0u64; LANES]; 5];
                for row in &mut rows {
                    for value in row {
                        *value = next() & ((1u64 << 52) - 1);
                    }
                }
                check_canonical(rows);
                round += 1;
            }
        }

        #[test]
        fn square_repeat_matches_strict_reference() {
            // square_repeat keeps every squaring but the last loose; verify
            // that's bit-identical to N strict squarings for every N actually
            // used by pow_p_minus_5_over_8/invert, plus the N=0/1 boundary.
            macro_rules! check {
                ($x:expr, $n:literal) => {
                    let x = $x;
                    assert!(
                        WideFe::square_repeat::<$n>(&x)
                            .equals_lanes(&strict_square_n(&x, $n))
                            .iter()
                            .all(|&v| v),
                        "square_repeat::<{}> diverged from strict reference",
                        $n
                    );
                };
            }
            for x in [
                WideFe::constant(crate::field::D_LIMBS),
                WideFe::constant(crate::field::SQRT_M1_LIMBS),
            ] {
                check!(x, 0);
                check!(x, 1);
                check!(x, 2);
                check!(x, 5);
                check!(x, 10);
                check!(x, 20);
                check!(x, 50);
                check!(x, 100);
            }
        }

        #[test]
        fn square_repeat_x2_matches_strict_reference() {
            let a = WideFe::constant(crate::field::D_LIMBS);
            let b = WideFe::constant(crate::field::SQRT_M1_LIMBS);
            macro_rules! check {
                ($n:literal) => {
                    let (xa, xb) = WideFe::square_repeat_x2::<$n>(&a, &b);
                    assert!(
                        xa.equals_lanes(&strict_square_n(&a, $n)).iter().all(|&v| v),
                        "square_repeat_x2::<{}> diverged from strict reference (lane a)",
                        $n
                    );
                    assert!(
                        xb.equals_lanes(&strict_square_n(&b, $n)).iter().all(|&v| v),
                        "square_repeat_x2::<{}> diverged from strict reference (lane b)",
                        $n
                    );
                };
            }
            check!(0);
            check!(1);
            check!(2);
            check!(5);
            check!(10);
            check!(20);
            check!(50);
            check!(100);
        }

        #[test]
        fn pow_x2_matches_sequential() {
            // The interleaved two-input exponentiation must be bit-identical to
            // two independent sequential pows on every lane.
            let a = WideFe::constant(crate::field::D_LIMBS);
            let b = WideFe::constant(crate::field::SQRT_M1_LIMBS);
            let (xa, xb) = WideFe::pow_p_minus_5_over_8_x2(&a, &b);
            assert!(
                xa.equals_lanes(&a.pow_p_minus_5_over_8())
                    .iter()
                    .all(|&v| v)
            );
            assert!(
                xb.equals_lanes(&b.pow_p_minus_5_over_8())
                    .iter()
                    .all(|&v| v)
            );
        }

        #[test]
        fn wide_pow_matches_scalar_reference() {
            // Keep scalar and SIMD decompression exponent chains in sync.
            let mut state = 0x9e3779b97f4a7c15u64;
            let mut next = move || {
                state = state
                    .wrapping_mul(0xd1342543de82ef95)
                    .wrapping_add(0x9e3779b97f4a7c15);
                state
            };

            let mut round = 0;
            while round < 200 {
                let fields: [crate::field::Fe51; LANES] = core::array::from_fn(|_| {
                    let limbs: [u64; 5] = core::array::from_fn(|_| next() & LIMB_MASK);
                    crate::field::Fe51::from_limbs(limbs)
                });
                let wide_result = WideFe::from_fields(&fields)
                    .pow_p_minus_5_over_8()
                    .to_fields();

                for (lane, field) in fields.iter().enumerate() {
                    assert!(
                        field.pow_p_minus_5_over_8().equals(&wide_result[lane]),
                        "lane {lane} diverged from scalar reference at round {round}"
                    );
                }
                round += 1;
            }
        }

        fn ord8a() -> EdwardsPoint {
            let bytes = [
                0x26, 0xe8, 0x95, 0x8f, 0xc2, 0xb2, 0x27, 0xb0, 0x45, 0xc3, 0xf4, 0x89, 0xf2, 0xef,
                0x98, 0xf0, 0xd5, 0xdf, 0xac, 0x05, 0xd3, 0xc6, 0x33, 0x39, 0xb1, 0x38, 0x02, 0x88,
                0x6d, 0x53, 0xfc, 0x05,
            ];
            EdwardsPoint::decompress(&bytes).expect("ord8a decodes")
        }

        #[test]
        fn wide_double_matches_scalar_on_torsion() {
            let p = ord8a();
            let scalar_doubled = p.double();
            let wide = WidePoint::from_points(&core::array::from_fn(|_| p.clone()));
            let wide_doubled = wide.double().to_points();
            assert_eq!(
                wide_doubled[0].compress(),
                scalar_doubled.compress(),
                "wide double diverges from scalar on an order-8 point"
            );
        }

        #[test]
        fn wide_multiscalar_identity_key_is_identity() {
            let id = EdwardsPoint::identity();
            let table = PointTable::new(&id);
            let base_table = BasepointTable::new();
            let s_digits = [[0i8; 64]; LANES];
            let mut one_bytes = [0u8; 32];
            one_bytes[0] = 1;
            let k = crate::scalar::Scalar::from_canonical_bytes(one_bytes);
            let k_digits = [k.to_radix16(); LANES];
            let prepared = PreparedBatch {
                public_key_tables: [&table; LANES],
                s_digits: &s_digits,
                k_digits: &k_digits,
            };
            let combined = mul_base_minus_public(&base_table, &prepared);
            let pts = combined.to_points();
            assert_eq!(
                pts[0].compress(),
                id.compress(),
                "sB - kA for s=0, A=identity must be identity"
            );
        }

        #[test]
        fn wide_subtract_then_cofactor_on_torsion() {
            let p = ord8a();
            let id = EdwardsPoint::identity();
            let scalar = id.subtract(&p).double().double().double();
            let wide_id = WidePoint::from_points(&core::array::from_fn(|_| id.clone()));
            let wide_p = WidePoint::from_points(&core::array::from_fn(|_| p.clone()));
            let wide_chain = wide_id
                .subtract(&wide_p)
                .double()
                .double()
                .double()
                .to_points();
            assert_eq!(scalar.compress(), id.compress(), "sanity: scalar -8p = id");
            assert_eq!(
                wide_chain[0].compress(),
                scalar.compress(),
                "wide subtract+cofactor diverges on order-8 point"
            );
        }

        #[test]
        fn wide_zip215_exact_failing_case() {
            let r_bytes = [
                0x26, 0xe8, 0x95, 0x8f, 0xc2, 0xb2, 0x27, 0xb0, 0x45, 0xc3, 0xf4, 0x89, 0xf2, 0xef,
                0x98, 0xf0, 0xd5, 0xdf, 0xac, 0x05, 0xd3, 0xc6, 0x33, 0x39, 0xb1, 0x38, 0x02, 0x88,
                0x6d, 0x53, 0xfc, 0x05,
            ];
            let mut a_bytes = [0u8; 32];
            a_bytes[0] = 1;
            let id = EdwardsPoint::decompress(&a_bytes).unwrap();
            let table = PointTable::new(&id);
            let base_table = BasepointTable::new();
            let s_digits = [[0i8; 64]; LANES];
            let digest =
                crate::sha512::hash_slices(&[&r_bytes, &a_bytes, b"taming the many eddsas"]);
            let k = crate::scalar::Scalar::from_wide_bytes(digest);
            let k_digits = [k.to_radix16(); LANES];
            let prepared = PreparedBatch {
                public_key_tables: [&table; LANES],
                s_digits: &s_digits,
                k_digits: &k_digits,
            };
            let (r_point, r_mask) = decompress_points_wide(&[r_bytes; LANES]);
            assert_eq!(r_mask, 0xff, "torsion R must decode");
            let r = WideRPoints(r_point);
            let result = verify_prepared_zip215(&prepared, &r, &base_table);
            assert!(
                result[0],
                "zip215 SIMD must accept this cofactored small-order case"
            );
        }

        #[test]
        fn wide_decompress_matches_scalar_on_torsion() {
            let bytes = [
                0x26, 0xe8, 0x95, 0x8f, 0xc2, 0xb2, 0x27, 0xb0, 0x45, 0xc3, 0xf4, 0x89, 0xf2, 0xef,
                0x98, 0xf0, 0xd5, 0xdf, 0xac, 0x05, 0xd3, 0xc6, 0x33, 0x39, 0xb1, 0x38, 0x02, 0x88,
                0x6d, 0x53, 0xfc, 0x05,
            ];
            let scalar = EdwardsPoint::decompress(&bytes).unwrap();
            let (wide, mask) = decompress_points_wide(&[bytes; LANES]);
            assert_eq!(mask, 0xff, "wide decode must succeed");
            let wide_pts = wide.to_points();
            assert_eq!(
                wide_pts[0].compress(),
                scalar.compress(),
                "wide decompress diverges from scalar on an order-8 point"
            );
        }
    }
}
