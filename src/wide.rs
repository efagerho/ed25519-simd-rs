pub(crate) mod avx512ifma {
    use crate::batch::PreparedVerificationBatch8WithoutR;
    #[cfg(test)]
    use crate::edwards::EdwardsPoint;
    use crate::edwards::{BasepointTable, CachedPoint, PointTable};
    use crate::field::Fe51;
    use crate::scalar::Radix16;
    use std::arch::x86_64::*;

    const LANES: usize = 8;
    const LIMB_MASK: u64 = (1u64 << 51) - 1;
    const FIELD_P_LIMBS: [u64; 5] = [LIMB_MASK - 18, LIMB_MASK, LIMB_MASK, LIMB_MASK, LIMB_MASK];

    pub(crate) struct WideRPoints8(WidePoint);

    /// Decompress eight `R` points and return a per-lane validity mask.
    pub(crate) fn decompress_r_points8(r_bytes: &[[u8; 32]; LANES]) -> (WideRPoints8, u8) {
        let (point, mask) = decompress_points8_wide(r_bytes);
        (WideRPoints8(point), mask)
    }

    /// Decode eight public keys and build cached tables with per-lane validity.
    pub(crate) fn decode_and_build_tables8(bytes: &[[u8; 32]; LANES]) -> ([PointTable; LANES], u8) {
        let (p, valid_mask) = decompress_points8_wide(bytes);
        (build_tables8_from_point(p), valid_mask)
    }

    /// Decode eight public keys and eight `R` points together, interleaving the
    /// two inverse-square-root chains (the latency-bound part of decompression).
    /// Returns the key tables + validity and the decompressed `R` + validity.
    pub(crate) fn decode_keys_and_decompress_r8(
        keys: &[[u8; 32]; LANES],
        r_bytes: &[[u8; 32]; LANES],
    ) -> ([PointTable; LANES], u8, WideRPoints8, u8) {
        let ((kp, kmask), (rp, rmask)) = decompress_points8_wide_x2(keys, r_bytes);
        (build_tables8_from_point(kp), kmask, WideRPoints8(rp), rmask)
    }

    /// Build the eight radix-16 cached tables from an already-decompressed
    /// 8-wide point (one base point per lane).
    fn build_tables8_from_point(p: WidePoint) -> [PointTable; LANES] {
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
        type Lane8 = [Fe51; LANES];
        let fields: [(Lane8, Lane8, Lane8, Lane8, Lane8); LANES] = core::array::from_fn(|i| {
            let m = &mult[i];
            let ypx = m.y.add(&m.x);
            let ymx = m.y.subtract(&m.x);
            let z2 = m.z.double();
            let t2d = m.t.multiply(&two_d);
            let neg_t2d = t2d.negate();
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
                CachedPoint::from_fields(
                    ypx[k].clone(),
                    ymx[k].clone(),
                    z2[k].clone(),
                    t2d[k].clone(),
                )
            });
            // -P's cached fields are P's with y±x swapped and t2d negated.
            let negative = core::array::from_fn(|i| {
                let (ypx, ymx, z2, _, neg_t2d) = &fields[i];
                CachedPoint::from_fields(
                    ymx[k].clone(),
                    ypx[k].clone(),
                    z2[k].clone(),
                    neg_t2d[k].clone(),
                )
            });
            PointTable::from_cached(cached, negative, identity.clone())
        })
    }

    // ZIP-215 cofactored verification: [8](sB - kA - R) == identity.
    pub(crate) fn verify_prepared8_zip215(
        prepared: &PreparedVerificationBatch8WithoutR<'_>,
        r: &WideRPoints8,
        base_table: &BasepointTable,
    ) -> [bool; LANES] {
        let combined = mul_base_minus_public8_without_r(base_table, prepared);
        let mut check = combined.subtract(&r.0);
        check = check
            .double_without_t()
            .double_without_t()
            .double_without_t();
        check.identity_lanes()
    }

    pub(crate) fn verify_prepared8_dalek(
        prepared: &PreparedVerificationBatch8WithoutR<'_>,
        r_bytes: &[[u8; 32]; LANES],
        base_table: &BasepointTable,
    ) -> [bool; LANES] {
        let combined = mul_base_minus_public8_without_r(base_table, prepared);
        let recomputed = combined.compress();
        core::array::from_fn(|lane| recomputed[lane] == r_bytes[lane])
    }

    pub(crate) fn verify_prepared8_dalek_projective(
        prepared: &PreparedVerificationBatch8WithoutR<'_>,
        r: &WideRPoints8,
        base_table: &BasepointTable,
    ) -> [bool; LANES] {
        let combined = mul_base_minus_public8_without_r(base_table, prepared);
        combined.equals_affine_lanes(&r.0)
    }

    /// Pre-`pow` state of a decompression: everything needed to finish once the
    /// inverse-square-root exponent has been raised. Splitting decompression into
    /// setup → pow → finish lets two independent decodes share one interleaved
    /// `pow_x2` (the latency-bound chain), hiding each chain's IFMA latency.
    struct DecompressSetup {
        u: WideFe,
        v: WideFe,
        base: WideFe, // u * v^3
        exp: WideFe,  // u * v^7  (raised to (p-5)/8)
        y: WideFe,
        x_signs: [bool; LANES],
    }

    fn decompress_setup8(bytes: &[[u8; 32]; LANES]) -> DecompressSetup {
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

    fn decompress_finish8(s: DecompressSetup, pow: WideFe) -> (WidePoint, u8) {
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

    /// Decompress eight compressed Edwards points with per-lane validity.
    fn decompress_points8_wide(bytes: &[[u8; 32]; LANES]) -> (WidePoint, u8) {
        let s = decompress_setup8(bytes);
        let pow = s.exp.pow_p_minus_5_over_8();
        decompress_finish8(s, pow)
    }

    /// Decompress two independent groups of eight points, interleaving the two
    /// inverse-square-root chains so each fills the other's IFMA latency gaps.
    fn decompress_points8_wide_x2(
        a_bytes: &[[u8; 32]; LANES],
        b_bytes: &[[u8; 32]; LANES],
    ) -> ((WidePoint, u8), (WidePoint, u8)) {
        let sa = decompress_setup8(a_bytes);
        let sb = decompress_setup8(b_bytes);
        let (pa, pb) = WideFe::pow_p_minus_5_over_8_x2(&sa.exp, &sb.exp);
        (decompress_finish8(sa, pa), decompress_finish8(sb, pb))
    }
    fn mul_base_minus_public8_without_r(
        base_table: &BasepointTable,
        prepared: &PreparedVerificationBatch8WithoutR<'_>,
    ) -> WidePoint {
        mul_base_minus_public8_parts(
            base_table,
            &prepared.public_key_tables,
            &prepared.s_digits,
            &prepared.k_digits,
        )
    }
    fn mul_base_minus_public8_parts(
        base_table: &BasepointTable,
        public_key_tables: &[&PointTable; LANES],
        s_digits: &[Radix16; LANES],
        k_digits: &[Radix16; LANES],
    ) -> WidePoint {
        let mut acc = WidePoint::identity();
        let public_tables_uniform = public_tables_uniform(public_key_tables);
        let mut pair = 33;
        while pair > 0 {
            pair -= 1;
            let odd_index = pair * 2 + 1;
            if odd_index < 65 {
                acc = acc.double4();

                add_public_digit(
                    &mut acc,
                    public_key_tables,
                    public_tables_uniform,
                    k_digits,
                    odd_index,
                );
            }

            acc = acc.double4();
            add_base_pair_digit(&mut acc, base_table, s_digits, pair);

            add_public_digit(
                &mut acc,
                public_key_tables,
                public_tables_uniform,
                k_digits,
                pair * 2,
            );
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
        match base_digit_pattern(s_digits, pair) {
            WideDigitPattern::Uniform(0) => {}
            WideDigitPattern::Uniform(digit) => {
                let selected = base_table.select_signed_cached_ref(digit);
                let selected = WideCachedPoint::broadcast(selected);
                acc.add_cached_assign(&selected);
            }
            WideDigitPattern::Mixed => {
                let first =
                    base_table.select_signed_cached_ref(base_pair_digit(&s_digits[0], pair));
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
        }
    }

    #[inline]
    fn add_public_digit(
        acc: &mut WidePoint,
        public_key_tables: &[&PointTable; LANES],
        public_tables_uniform: bool,
        k_digits: &[Radix16; LANES],
        index: usize,
    ) {
        match digit_pattern(k_digits, index) {
            DigitPattern::Uniform(0) => {}
            DigitPattern::Uniform(digit) if public_tables_uniform => {
                let selected = public_key_tables[0].select_signed_cached_ref(-digit);
                let selected = WideCachedPoint::broadcast(selected);
                acc.add_cached_assign(&selected);
            }
            DigitPattern::Uniform(_) | DigitPattern::Mixed => {
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
        }
    }

    #[derive(Clone, Copy, Eq, PartialEq)]
    enum DigitPattern {
        Uniform(i8),
        Mixed,
    }

    #[derive(Clone, Copy, Eq, PartialEq)]
    enum WideDigitPattern {
        Uniform(i16),
        Mixed,
    }

    #[inline(always)]
    fn digit_pattern(digits: &[Radix16; LANES], index: usize) -> DigitPattern {
        let first = digits[0][index];
        let mut lane = 1;
        while lane < LANES {
            if digits[lane][index] != first {
                return DigitPattern::Mixed;
            }
            lane += 1;
        }
        DigitPattern::Uniform(first)
    }

    #[inline(always)]
    fn base_digit_pattern(digits: &[Radix16; LANES], pair: usize) -> WideDigitPattern {
        let first = base_pair_digit(&digits[0], pair);
        let mut lane = 1;
        while lane < LANES {
            if base_pair_digit(&digits[lane], pair) != first {
                return WideDigitPattern::Mixed;
            }
            lane += 1;
        }
        WideDigitPattern::Uniform(first)
    }

    // Fold two adjacent signed radix-16 digits into one radix-256 digit
    // `even + (odd << 4)`, magnitude at most `8 + 8*16 = 136` — which is exactly
    // `BASEPOINT_TABLE_SIZE`, the number of base-point multiples tabulated.
    #[inline(always)]
    fn base_pair_digit(digits: &Radix16, pair: usize) -> i16 {
        let even_index = pair * 2;
        let odd_index = even_index + 1;
        let odd = if odd_index < digits.len() {
            (digits[odd_index] as i16) << 4
        } else {
            0
        };
        digits[even_index] as i16 + odd
    }

    #[inline(always)]
    fn public_tables_uniform(public_key_tables: &[&PointTable; LANES]) -> bool {
        let first = public_key_tables[0] as *const PointTable;
        let mut lane = 1;
        while lane < LANES {
            if !core::ptr::eq(first, public_key_tables[lane] as *const PointTable) {
                return false;
            }
            lane += 1;
        }
        true
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
        fn broadcast_field(field: &Fe51) -> Self {
            unsafe {
                let limbs = field.reduced_limbs();
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
        // Deferred-reduction (fused) field ops. A `*_loose` multiply/square skips
        // the final `reduce_loose` pass of `reduce_ifma`, doing only the single
        // IFMA carry pass; the additive op that consumes it folds that missing
        // reduction into the carry pass it runs anyway, saving one whole pass per
        // multiply→add/sub edge in the point formulas.
        //
        // Bounds. Inputs are < 2^52, so each 52x52 IFMA product is < 2^104 and a
        // column sums at most five of them: lo[i], hi[i] < 5*2^52 < 2^55. After
        // the one carry pass in `reduce_ifma_loose`, limbs 1..4 are masked to
        // < 2^51, while limb0 = (masked < 2^51) + 19*carry4 with carry4 < 2^55,
        // i.e. **limb0 < 2^51 + 19*2^55 < 2^60**. So a loose operand is < 2^60 in
        // limb0 and < 2^51 elsewhere — valid for an additive consumer but NOT a
        // valid IFMA input (which needs < 2^52).
        //
        // The `*_wide` subtracts therefore widen the borrow bias from 4*p/8*p to
        // 2048*p (limb0 = 2048*(2^51-19) ~= 2^62). That exceeds the sum of up to
        // two loose subtrahends (< 2*2^60 = 2^61), so every limb stays
        // non-negative; the trailing `reduce_loose` then folds the result (limbs
        // < ~2^62) back below 2^52 in one pass, a valid IFMA input again.
        fn square_loose(&self) -> Self {
            unsafe {
                let z = _mm512_setzero_si512();
                let mut lo = [z; 5];
                let mut hi = [z; 5];

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

                Self::reduce_ifma_loose(lo, hi)
            }
        }
        fn multiply_loose(&self, rhs: &Self) -> Self {
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

                Self::reduce_ifma_loose(lo, hi)
            }
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

                Self::reduce_ifma(lo, hi)
            }
        }
        fn multiply(&self, rhs: &Self) -> Self {
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

                Self::reduce_ifma(lo, hi)
            }
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
        fn square_repeat<const N: usize>(&self) -> Self {
            let mut out = *self;
            let mut i = 0;
            while i < N {
                out = out.square();
                i += 1;
            }
            out
        }

        // --- interleaved two-input variants: run two independent field-exp
        // chains in lockstep so each fills the other's IFMA latency gaps. Used to
        // fuse the key-decode and R-decode square roots (latency-bound chains). ---
        fn square_repeat_x2<const N: usize>(a: &Self, b: &Self) -> (Self, Self) {
            let (mut x, mut y) = (*a, *b);
            let mut i = 0;
            while i < N {
                x = x.square();
                y = y.square();
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
            let limbs = self.canonical_limb_rows();
            core::array::from_fn(|lane| {
                limbs[0][lane] == 0
                    && limbs[1][lane] == 0
                    && limbs[2][lane] == 0
                    && limbs[3][lane] == 0
                    && limbs[4][lane] == 0
            })
        }
        fn is_odd_lanes(self) -> [bool; LANES] {
            let limbs = self.canonical_limb_rows();
            core::array::from_fn(|lane| (limbs[0][lane] & 1) != 0)
        }
        fn canonical_limb_rows(self) -> [[u64; LANES]; 5] {
            let mut rows = [[0u64; LANES]; 5];
            storeu(self.limbs[0], &mut rows[0]);
            storeu(self.limbs[1], &mut rows[1]);
            storeu(self.limbs[2], &mut rows[2]);
            storeu(self.limbs[3], &mut rows[3]);
            storeu(self.limbs[4], &mut rows[4]);

            let mut lane = 0;
            while lane < LANES {
                let canonical = canonicalize_field_limbs([
                    rows[0][lane],
                    rows[1][lane],
                    rows[2][lane],
                    rows[3][lane],
                    rows[4][lane],
                ]);
                let mut limb = 0;
                while limb < 5 {
                    rows[limb][lane] = canonical[limb];
                    limb += 1;
                }
                lane += 1;
            }

            rows
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

                // One extra carry pass after the IFMA carry above leaves every limb
                // < 2^52; multiply/square consumers tolerate that, and `square`
                // re-normalizes its inputs. (Full 2-pass `reduce64` is unnecessary.)
                Self::reduce_loose(lo)
            }
        }
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
        fn broadcast(point: &CachedPoint) -> Self {
            let (y_plus_x, y_minus_x, z2, t2d) = point.coords();
            Self {
                y_plus_x: WideFe::broadcast_field(y_plus_x),
                y_minus_x: WideFe::broadcast_field(y_minus_x),
                z2: WideFe::broadcast_field(z2),
                t2d: WideFe::broadcast_field(t2d),
            }
        }
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
        #[cfg(test)]
        fn from_points(points: &[EdwardsPoint; LANES]) -> Self {
            let xs = core::array::from_fn(|lane| points[lane].coords().0.clone());
            let ys = core::array::from_fn(|lane| points[lane].coords().1.clone());
            let zs = core::array::from_fn(|lane| points[lane].coords().2.clone());
            let ts = core::array::from_fn(|lane| points[lane].coords().3.clone());
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
                EdwardsPoint::from_coords_unchecked(
                    xs[lane].clone(),
                    ys[lane].clone(),
                    zs[lane].clone(),
                    ts[lane].clone(),
                )
            })
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
            // a,b,c,d feed only additive ops, so defer their final carry pass.
            let a = self.y.subtract(&self.x).multiply_loose(&rhs.y_minus_x);
            let b = self.y.add_loose(&self.x).multiply_loose(&rhs.y_plus_x);
            let e = b.subtract_wide(&a);
            let h = b.add_loose(&a);
            let c = self.t.multiply_loose(&rhs.t2d);
            let d = self.z.multiply_loose(&rhs.z2);
            let f = d.subtract_wide(&c);
            let g = d.add_loose(&c);

            self.x = e.multiply(&f);
            self.z = f.multiply(&g);
            self.y = g.multiply(&h);
            self.t = e.multiply(&h);
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
            // The squares feed only additive ops, so defer their final carry pass.
            let a = self.x.square_loose();
            let b = self.y.square_loose();
            let c = self.z.square_loose().double_loose();
            let e = self
                .x
                .add_loose(&self.y)
                .square_loose()
                .subtract_sum_wide(&a, &b);
            let g = b.subtract_wide(&a);
            let f = g.subtract(&c);
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

    fn canonicalize_field_limbs(limbs: [u64; 5]) -> [u64; 5] {
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
            let s_digits = [[0i8; 65]; LANES];
            let mut one_bytes = [0u8; 32];
            one_bytes[0] = 1;
            let k = crate::scalar::Scalar::from_canonical_bytes(one_bytes);
            let k_digits = [k.to_radix16(); LANES];
            let prepared = PreparedVerificationBatch8WithoutR {
                public_key_tables: [&table; LANES],
                s_digits,
                k_digits,
            };
            let combined = mul_base_minus_public8_without_r(&base_table, &prepared);
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
            let s_digits = [[0i8; 65]; LANES];
            let digest =
                crate::sha512::hash_slices(&[&r_bytes, &a_bytes, b"taming the many eddsas"]);
            let k = crate::scalar::Scalar::from_wide_bytes(digest);
            let k_digits = [k.to_radix16(); LANES];
            let prepared = PreparedVerificationBatch8WithoutR {
                public_key_tables: [&table; LANES],
                s_digits,
                k_digits,
            };
            let (r_point, r_mask) = decompress_points8_wide(&[r_bytes; LANES]);
            assert_eq!(r_mask, 0xff, "torsion R must decode");
            let r = WideRPoints8(r_point);
            let result = verify_prepared8_zip215(&prepared, &r, &base_table);
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
            let (wide, mask) = decompress_points8_wide(&[bytes; LANES]);
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
