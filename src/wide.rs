pub(crate) mod avx512ifma {
    use crate::batch::{PUBLIC_KEY_LEN, PreparedBatch, R_ENCODING_LEN};
    #[cfg(test)]
    use crate::edwards::EdwardsPoint;
    use crate::edwards::{
        AffineCachedPoint, BasepointTable, CachedPoint, POINT_ENCODING_LEN, PointTable,
    };
    use crate::field::{Fe51, LIMB_COUNT};
    use crate::scalar::Radix16;
    use std::arch::x86_64::*;

    const LANES: usize = crate::batch::SIMD_LANES;
    // These intrinsics hard-code eight lanes; reject a changed `SIMD_LANES`.
    const _: () = assert!(LANES == 8, "avx512ifma assumes exactly 8 SIMD lanes");
    const LIMB_MASK: u64 = (1u64 << 51) - 1;
    pub(crate) struct WideRPoints {
        point: WidePoint,
        x_zero_mask: Option<u8>,
    }

    impl WideRPoints {
        /// Dalek-invalid negative-zero lanes.
        pub(crate) fn x_zero_lanes(&self) -> [bool; LANES] {
            let mask = self
                .x_zero_mask
                .expect("x-zero lanes were not tracked for this decode");
            mask_to_lanes(mask as __mmask8)
        }
    }

    /// Decompress one SIMD chunk of `R` points and return a per-lane validity mask.
    pub(crate) fn decompress_r_points(
        r_bytes: &[[u8; R_ENCODING_LEN]; LANES],
    ) -> (WideRPoints, u8) {
        let (point, mask) = decompress_points_wide(r_bytes);
        (
            WideRPoints {
                point,
                x_zero_mask: None,
            },
            mask,
        )
    }

    /// Decode keys and `R` together, interleaving their inverse-square-root chains.
    pub(crate) fn decode_keys_and_decompress_r(
        keys: &[[u8; PUBLIC_KEY_LEN]; LANES],
        r_bytes: &[[u8; R_ENCODING_LEN]; LANES],
        dalek: bool,
        key_tables: &mut [Option<PointTable>; LANES],
    ) -> (u8, WideRPoints, u8) {
        let ((kp, kmask), (rp, rmask, x_zero_mask)) =
            decompress_point_batches_wide(keys, r_bytes, dalek);
        build_tables_from_point(kp, key_tables);
        (
            kmask,
            WideRPoints {
                point: rp,
                x_zero_mask,
            },
            rmask,
        )
    }

    /// Build the per-lane radix-16 cached tables from an already-decompressed
    /// SIMD point.
    /// Every slot is filled, including lanes whose decode failed; the caller
    /// discards those by mask.
    fn build_tables_from_point(p: WidePoint, tables: &mut [Option<PointTable>; LANES]) {
        // Build P..8P as a depth-4 tree; doublings cost 4S+4M instead of 8M.
        let p2 = p.double_affine();
        let p4 = p2.double();
        let p3 = p2.add_affine_rhs(&p);
        let mult = [
            p,
            p2,
            p3,
            p4,
            p4.add_affine_rhs(&p), // 5P
            p3.double(),           // 6P
            p4.add(&p3),           // 7P
            p4.double(),           // 8P
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
                // Table consumers accept these strict values as loose fields.
                (
                    ypx.to_fields_loose(),
                    ymx.to_fields_loose(),
                    z2.to_fields_loose(),
                    t2d.to_fields_loose(),
                    neg_t2d.to_fields_loose(),
                )
            });

        let identity = CachedPoint::identity();
        for k in 0..LANES {
            let cached = core::array::from_fn(|i| {
                let (ypx, ymx, z2, t2d, _) = &fields[i];
                CachedPoint::from_fields(ypx[k], ymx[k], z2[k], t2d[k])
            });
            // -P's cached fields are P's with y±x swapped and t2d negated.
            let negative = core::array::from_fn(|i| {
                let (ypx, ymx, z2, _, neg_t2d) = &fields[i];
                CachedPoint::from_fields(ymx[k], ypx[k], z2[k], neg_t2d[k])
            });
            tables[k] = Some(PointTable::from_cached(cached, negative, identity.clone()));
        }
    }

    // ZIP-215 cofactored verification: [8](sB - kA - R) == identity.
    pub(crate) fn verify_prepared_zip215(
        prepared: &PreparedBatch<'_>,
        r: &WideRPoints,
        base_table: &BasepointTable,
    ) -> [bool; LANES] {
        let combined = mul_base_minus_public::<true>(base_table, prepared);
        combined.subtract_affine_and_check_8_torsion(&r.point)
    }

    pub(crate) fn verify_prepared_dalek(
        prepared: &PreparedBatch<'_>,
        r_bytes: &[[u8; R_ENCODING_LEN]; LANES],
        base_table: &BasepointTable,
    ) -> [bool; LANES] {
        let combined = mul_base_minus_public::<false>(base_table, prepared);
        let recomputed = combined.compress();
        core::array::from_fn(|lane| recomputed[lane] == r_bytes[lane])
    }

    pub(crate) fn verify_prepared_dalek_projective(
        prepared: &PreparedBatch<'_>,
        r: &WideRPoints,
        base_table: &BasepointTable,
    ) -> [bool; LANES] {
        let combined = mul_base_minus_public::<false>(base_table, prepared);
        combined.equals_affine_lanes(&r.point)
    }

    /// Decompression state before the inverse-square-root exponentiation.
    struct DecompressSetup {
        u: WideFe,
        v: WideFe,
        base: WideFe, // u * v^3
        exp: WideFe,  // u * v^7  (raised to (p-5)/8)
        y: WideFe,
        x_signs: u8,
    }

    fn decompress_setup(bytes: &[[u8; POINT_ENCODING_LEN]; LANES]) -> DecompressSetup {
        let mut y_fields = core::array::from_fn(|_| Fe51::zero());
        let mut x_signs = 0u8;

        for (lane, byte_arr) in bytes.iter().enumerate() {
            x_signs |= (byte_arr[31] >> 7) << lane;
            let mut y_bytes = *byte_arr;
            y_bytes[31] &= 0x7f;
            // ZIP-215/Dalek decoding treats y modulo p.
            y_fields[lane] = Fe51::from_bytes_unchecked(&y_bytes);
        }

        let y = WideFe::from_fields(&y_fields);
        let yy = y.square();
        let u = yy.subtract(&WideFe::one());
        let v = WideFe::one().add(&WideFe::d().multiply(&yy));
        // u*v^7 = (u*v^3)*v^4, saving one multiply.
        let v2 = v.square();
        let v4 = v2.square();
        let v3 = v2.multiply(&v);
        let base = u.multiply(&v3);
        let exp = base.multiply(&v4);
        DecompressSetup {
            u,
            v,
            base,
            exp,
            y,
            x_signs,
        }
    }

    fn decompress_finish<const COMPUTE_T: bool, const TRACK_X_ZERO: bool>(
        s: DecompressSetup,
        pow: WideFe,
    ) -> (WidePoint, u8, Option<u8>) {
        let mut x = s.base.multiply(&pow);

        let vx2 = s.v.multiply(&x.square());
        let first_ok = vx2.equals_mask(&s.u);

        let x_alt = x.multiply(&WideFe::sqrt_m1());
        // The alternate root is valid iff the existing `vx2` equals `-u`.
        let second_ok = vx2.add_loose(&s.u).is_zero_mask();

        let alt_mask = !first_ok & second_ok;
        let valid_mask = first_ok | second_ok;

        x = x.blend(alt_mask, &x_alt);

        // Points outside `valid_mask` are garbage.
        let (x_odd, x_zero_mask) = if TRACK_X_ZERO {
            let (odd, zero) = x.odd_and_zero_masks();
            (odd, Some(zero))
        } else {
            (x.is_odd_mask(), None)
        };
        let x_neg = x.negate();
        let negate_mask = x_odd ^ s.x_signs;
        x = x.blend(negate_mask, &x_neg);

        let t = if COMPUTE_T {
            x.multiply(&s.y)
        } else {
            WideFe::zero()
        };
        (
            WidePoint {
                x,
                y: s.y,
                z: WideFe::one(),
                t,
            },
            valid_mask,
            x_zero_mask,
        )
    }

    /// Decompress one SIMD chunk of compressed Edwards points with per-lane validity.
    fn decompress_points_wide(bytes: &[[u8; POINT_ENCODING_LEN]; LANES]) -> (WidePoint, u8) {
        let s = decompress_setup(bytes);
        let pow = s.exp.pow_p_minus_5_over_8();
        let (point, mask, _) = decompress_finish::<true, false>(s, pow);
        (point, mask)
    }

    /// Decompress two independent SIMD chunks, interleaving the two
    /// inverse-square-root chains so each fills the other's IFMA latency gaps.
    fn decompress_point_batches_wide(
        a_bytes: &[[u8; POINT_ENCODING_LEN]; LANES],
        b_bytes: &[[u8; POINT_ENCODING_LEN]; LANES],
        minimize_b_for_dalek: bool,
    ) -> ((WidePoint, u8), (WidePoint, u8, Option<u8>)) {
        let sa = decompress_setup(a_bytes);
        let sb = decompress_setup(b_bytes);
        let (pa, pb) = WideFe::pow_p_minus_5_over_8_x2(&sa.exp, &sb.exp);
        let (a, a_mask, _) = decompress_finish::<true, false>(sa, pa);
        let b = if minimize_b_for_dalek {
            decompress_finish::<false, true>(sb, pb)
        } else {
            decompress_finish::<true, false>(sb, pb)
        };
        ((a, a_mask), b)
    }
    // Only ZIP-215's final torsion subtraction needs T.
    fn mul_base_minus_public<const NEED_T: bool>(
        base_table: &BasepointTable,
        prepared: &PreparedBatch<'_>,
    ) -> WidePoint {
        let public_key_tables = &prepared.public_key_tables;
        let s_digits = prepared.s_digits;
        let k_digits = prepared.k_digits;

        // Recover a projective point from the cached top digit; the next
        // doubling does not need `T`.
        let selected: [_; LANES] = core::array::from_fn(|lane| {
            public_key_tables[lane].select_signed_cached_ref(-k_digits[lane][63])
        });
        let mut acc = WidePoint::from_cached_refs_without_t(&selected);

        // Continue at digit 62; reduced scalars have no digit above 63.
        acc = acc.double4();
        add_base_pair_digit(&mut acc, base_table, s_digits, 31);
        add_public_digit_before_double(&mut acc, public_key_tables, k_digits, 62);

        // These public-key additions feed doublings, which do not use `T`.
        for pair in (1..31).rev() {
            acc = acc.double4();
            add_public_digit_before_double(&mut acc, public_key_tables, k_digits, pair * 2 + 1);

            acc = acc.double4();
            add_base_pair_digit(&mut acc, base_table, s_digits, pair);
            add_public_digit_before_double(&mut acc, public_key_tables, k_digits, pair * 2);
        }

        acc = acc.double4();
        add_public_digit_before_double(&mut acc, public_key_tables, k_digits, 1);
        acc = acc.double4();
        add_base_pair_digit(&mut acc, base_table, s_digits, 0);
        if NEED_T {
            add_public_digit(&mut acc, public_key_tables, k_digits, 0);
        } else {
            add_public_digit_before_double(&mut acc, public_key_tables, k_digits, 0);
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
        let selected: [_; LANES] = core::array::from_fn(|lane| {
            base_table.select_signed_affine_ref(base_pair_digit(&s_digits[lane], pair))
        });
        acc.add_affine_cached_refs_assign(&selected);
    }

    #[inline]
    fn add_public_digit(
        acc: &mut WidePoint,
        public_key_tables: &[&PointTable; LANES],
        k_digits: &[Radix16; LANES],
        index: usize,
    ) {
        let selected: [_; LANES] = core::array::from_fn(|lane| {
            public_key_tables[lane].select_signed_cached_ref(-k_digits[lane][index])
        });
        acc.add_cached_refs_assign(&selected, true);
    }

    #[inline]
    fn add_public_digit_before_double(
        acc: &mut WidePoint,
        public_key_tables: &[&PointTable; LANES],
        k_digits: &[Radix16; LANES],
        index: usize,
    ) {
        let selected: [_; LANES] = core::array::from_fn(|lane| {
            public_key_tables[lane].select_signed_cached_ref(-k_digits[lane][index])
        });
        acc.add_cached_refs_assign(&selected, false);
    }

    // Fold a radix-16 digit pair into a bounded radix-256 base-table digit.
    #[inline(always)]
    fn base_pair_digit(digits: &Radix16, pair: usize) -> i16 {
        digits[pair * 2] as i16 + ((digits[pair * 2 + 1] as i16) << 4)
    }

    #[derive(Clone, Copy)]
    struct WideFe {
        limbs: [__m512i; LIMB_COUNT],
    }

    impl WideFe {
        fn zero() -> Self {
            unsafe {
                let z = _mm512_setzero_si512();
                Self {
                    limbs: [z; LIMB_COUNT],
                }
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
        /// Transpose eight lanes of scalar limbs. Inlined so both entry points
        /// below cost the same as an open-coded loop.
        #[inline(always)]
        fn from_limbs_per_lane(limbs_of: impl Fn(usize) -> [u64; LIMB_COUNT]) -> Self {
            let mut by_limb = [[0u64; LANES]; LIMB_COUNT];
            let mut lane = 0;
            while lane < LANES {
                let limbs = limbs_of(lane);
                let mut limb = 0;
                while limb < LIMB_COUNT {
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
        fn from_fields(fields: &[Fe51; LANES]) -> Self {
            Self::from_limbs_per_lane(|lane| fields[lane].reduced_limbs())
        }
        fn from_field_refs(fields: &[&Fe51; LANES]) -> Self {
            Self::from_limbs_per_lane(|lane| fields[lane].reduced_limbs())
        }
        #[cfg(test)]
        fn to_fields(self) -> [Fe51; LANES] {
            let mut by_limb = [[0u64; LANES]; LIMB_COUNT];
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
            let mut by_limb = [[0u64; LANES]; LIMB_COUNT];
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
        fn to_bytes_lanes(self) -> [[u8; POINT_ENCODING_LEN]; LANES] {
            unsafe {
                let c = self.canonical();
                // Packing overlaps unless canonical limb 0 is below 2^51.
                debug_assert!(
                    c.limb_below(0, 51),
                    "to_bytes_lanes needs a canonical limb 0 below 2^51"
                );
                let packed = [
                    _mm512_or_si512(c.limbs[0], _mm512_slli_epi64(c.limbs[1], 51)),
                    _mm512_or_si512(
                        _mm512_srli_epi64(c.limbs[1], 13),
                        _mm512_slli_epi64(c.limbs[2], 38),
                    ),
                    _mm512_or_si512(
                        _mm512_srli_epi64(c.limbs[2], 26),
                        _mm512_slli_epi64(c.limbs[3], 25),
                    ),
                    _mm512_or_si512(
                        _mm512_srli_epi64(c.limbs[3], 39),
                        _mm512_slli_epi64(c.limbs[4], 12),
                    ),
                ];
                let mut words = [[0u64; LANES]; 4];
                storeu(packed[0], &mut words[0]);
                storeu(packed[1], &mut words[1]);
                storeu(packed[2], &mut words[2]);
                storeu(packed[3], &mut words[3]);

                core::array::from_fn(|lane| {
                    let mut bytes = [0u8; POINT_ENCODING_LEN];
                    let mut word = 0;
                    while word < 4 {
                        bytes[word * 8..word * 8 + 8]
                            .copy_from_slice(&words[word][lane].to_le_bytes());
                        word += 1;
                    }
                    bytes
                })
            }
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
                let reduced = Self::reduce_loose(h);
                Self::carry_limb0(reduced.limbs)
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
        fn square_accum(&self) -> ([__m512i; LIMB_COUNT], [__m512i; LIMB_COUNT]) {
            unsafe {
                let z = _mm512_setzero_si512();
                let mut lo = [z; LIMB_COUNT];
                let mut hi = [z; LIMB_COUNT];

                // Normalize loose limb0 to keep doubled IFMA inputs under 52 bits.
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
        // Strict and loose multiplication differ only in final reduction.
        fn multiply_accum(&self, rhs: &Self) -> ([__m512i; LIMB_COUNT], [__m512i; LIMB_COUNT]) {
            unsafe {
                let z = _mm512_setzero_si512();
                let mut lo = [z; LIMB_COUNT];
                let mut hi = [z; LIMB_COUNT];

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

        // One IFMA carry pass leaves limb0 < 2^60 and limbs 1..4 < 2^51.
        fn reduce_ifma_loose(mut lo: [__m512i; LIMB_COUNT], hi: [__m512i; LIMB_COUNT]) -> Self {
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

        // `self + 2048*p - rhs`. The wide forms below use a 2048*p bias, enough
        // for two loose subtrahends (limb0 < 2^60); `subtract`'s 4*p is not.
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

        // Fold `2*rhs` into the wide subtraction to avoid a separate carry pass.
        fn subtract_sum_doubled_wide(&self, lhs: &Self, rhs: &Self) -> Self {
            unsafe {
                let b0 = _mm512_set1_epi64((2048 * (LIMB_MASK - 18)) as i64);
                let bn = _mm512_set1_epi64((2048 * LIMB_MASK) as i64);
                let bias = [b0, bn, bn, bn, bn];
                let h = core::array::from_fn(|i| {
                    _mm512_sub_epi64(
                        _mm512_sub_epi64(_mm512_add_epi64(self.limbs[i], bias[i]), lhs.limbs[i]),
                        _mm512_slli_epi64(rhs.limbs[i], 1),
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
        // Keep intermediates loose; reduce only the final result for multiplication.
        fn square_repeat<const N: usize>(&self) -> Self {
            let mut out = *self;
            for i in 0..N {
                out = if i + 1 < N {
                    out.square_loose()
                } else {
                    out.square()
                };
            }
            out
        }

        // Interleave two exponentiation chains to hide IFMA latency.
        fn square_repeat_x2<const N: usize>(a: &Self, b: &Self) -> (Self, Self) {
            let (mut x, mut y) = (*a, *b);
            for i in 0..N {
                if i + 1 < N {
                    x = x.square_loose();
                    y = y.square_loose();
                } else {
                    x = x.square();
                    y = y.square();
                }
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
            mask_to_lanes(self.equals_mask(rhs) as __mmask8)
        }
        fn equals_mask(self, rhs: &Self) -> u8 {
            self.subtract(rhs).is_zero_mask()
        }
        fn is_zero_lanes(self) -> [bool; LANES] {
            mask_to_lanes(self.is_zero_mask() as __mmask8)
        }
        fn is_zero_mask(self) -> u8 {
            self.canonical().canonical_zero_mask()
        }
        /// Zero mask of an already-canonicalized value.
        #[inline(always)]
        fn canonical_zero_mask(&self) -> u8 {
            unsafe {
                let zero = _mm512_setzero_si512();
                let mask = _mm512_cmpeq_epu64_mask(self.limbs[0], zero)
                    & _mm512_cmpeq_epu64_mask(self.limbs[1], zero)
                    & _mm512_cmpeq_epu64_mask(self.limbs[2], zero)
                    & _mm512_cmpeq_epu64_mask(self.limbs[3], zero)
                    & _mm512_cmpeq_epu64_mask(self.limbs[4], zero);
                mask as u8
            }
        }
        #[cfg(test)]
        fn is_odd_lanes(self) -> [bool; LANES] {
            mask_to_lanes(self.is_odd_mask() as __mmask8)
        }
        fn limb_below(&self, index: usize, bits: u32) -> bool {
            let mut lanes = [0u64; LANES];
            storeu(self.limbs[index], &mut lanes);
            lanes.iter().all(|&limb| limb < (1u64 << bits))
        }

        fn is_odd_mask(self) -> u8 {
            unsafe {
                let c = self.canonical();
                let one = _mm512_set1_epi64(1);
                _mm512_test_epi64_mask(c.limbs[0], one) as u8
            }
        }
        /// Return parity and zero masks from one canonicalization.
        fn odd_and_zero_masks(self) -> (u8, u8) {
            unsafe {
                let c = self.canonical();
                let one = _mm512_set1_epi64(1);
                (
                    _mm512_test_epi64_mask(c.limbs[0], one) as u8,
                    c.canonical_zero_mask(),
                )
            }
        }
        /// Vectorized `Fe51::canonical`; bounded high limbs reduce `>= p` to a
        /// high-limb check and limb-0 threshold.
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
        fn reduce_ifma(lo: [__m512i; LIMB_COUNT], hi: [__m512i; LIMB_COUNT]) -> Self {
            // Only limb 0 retains a residual; carry it to restore IFMA bounds.
            Self::carry_limb0(Self::reduce_ifma_loose(lo, hi).limbs)
        }
        /// Carry loose limb 0, restoring the `< 2^52` IFMA input bound.
        fn carry_limb0(mut h: [__m512i; LIMB_COUNT]) -> Self {
            unsafe {
                let mask = _mm512_set1_epi64(LIMB_MASK as i64);
                let carry = _mm512_srli_epi64(h[0], 51);
                h[0] = _mm512_and_si512(h[0], mask);
                h[1] = _mm512_add_epi64(h[1], carry);
                Self { limbs: h }
            }
        }
        /// One carry pass: limbs 1..4 become `< 2^51`; limb 0 may keep the
        /// small wraparound residual needed by additive consumers.
        fn reduce_loose(mut h: [__m512i; LIMB_COUNT]) -> Self {
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
        fn reduce64(h: [__m512i; LIMB_COUNT]) -> Self {
            Self::reduce_loose(Self::reduce_loose(h).limbs)
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
    enum SelectedCachedRefs<'a> {
        Projective(&'a [&'a CachedPoint; LANES]),
        Affine(&'a [&'a AffineCachedPoint; LANES]),
    }

    impl SelectedCachedRefs<'_> {
        /// Transpose one cached coordinate. The pickers differ because an affine
        /// point omits `2*Z`, shifting `t2d` down a slot.
        #[inline(always)]
        fn transpose(
            self,
            projective: impl Fn(&CachedPoint) -> &Fe51,
            affine: impl Fn(&AffineCachedPoint) -> &Fe51,
        ) -> WideFe {
            match self {
                Self::Projective(points) => {
                    WideFe::from_field_refs(&core::array::from_fn(|lane| projective(points[lane])))
                }
                Self::Affine(points) => {
                    WideFe::from_field_refs(&core::array::from_fn(|lane| affine(points[lane])))
                }
            }
        }

        #[inline(always)]
        fn y_plus_x(self) -> WideFe {
            self.transpose(|p| p.coords().0, |p| p.coords().0)
        }

        #[inline(always)]
        fn y_minus_x(self) -> WideFe {
            self.transpose(|p| p.coords().1, |p| p.coords().1)
        }

        #[inline(always)]
        fn t2d(self) -> WideFe {
            self.transpose(|p| p.coords().3, |p| p.coords().2)
        }

        /// The cached `2*Z`, or `None` for an affine point whose `Z` is one.
        #[inline(always)]
        fn projective_z2(self) -> Option<WideFe> {
            match self {
                Self::Projective(points) => {
                    Some(WideFe::from_field_refs(&core::array::from_fn(|lane| {
                        points[lane].coords().2
                    })))
                }
                Self::Affine(_) => None,
            }
        }
    }

    impl WidePoint {
        /// Recover `(X:Y:Z)` without `T`; callers must double before an
        /// extended-coordinate operation.
        #[inline(never)]
        fn from_cached_refs_without_t(points: &[&CachedPoint; LANES]) -> Self {
            let field = |pick: fn(&CachedPoint) -> &Fe51| {
                WideFe::from_field_refs(&core::array::from_fn(|lane| pick(points[lane])))
            };
            let y_plus_x = field(|p| p.coords().0);
            let y_minus_x = field(|p| p.coords().1);

            Self {
                x: y_plus_x.subtract(&y_minus_x),
                y: y_plus_x.add_loose(&y_minus_x),
                z: field(|p| p.coords().2),
                t: WideFe::zero(),
            }
        }
        fn compress(&self) -> [[u8; POINT_ENCODING_LEN]; LANES] {
            let zinv = self.z.invert();
            let x = self.x.multiply(&zinv);
            let y = self.y.multiply(&zinv);
            let x_odd = x.is_odd_mask();
            let mut bytes = y.to_bytes_lanes();
            for (lane, encoding) in bytes.iter_mut().enumerate() {
                encoding[31] |= ((x_odd >> lane) & 1) << 7;
            }
            bytes
        }
        /// Compare with a freshly decompressed point whose `z` is one.
        fn equals_affine_lanes(&self, affine: &Self) -> [bool; LANES] {
            debug_assert!(
                affine.z.equals_lanes(&WideFe::one()).iter().all(|&eq| eq),
                "equals_affine_lanes requires z == 1 in every lane"
            );
            let x = affine.x.multiply(&self.z);
            let y = affine.y.multiply(&self.z);
            let x_equal = self.x.equals_lanes(&x);
            let y_equal = self.y.equals_lanes(&y);
            core::array::from_fn(|lane| x_equal[lane] && y_equal[lane])
        }
        // Table-building points are strict, so small-bias `subtract` is valid.
        fn add(&self, rhs: &Self) -> Self {
            self.add_impl::<false>(rhs)
        }
        fn add_affine_rhs(&self, rhs: &Self) -> Self {
            debug_assert!(
                rhs.z.equals_lanes(&WideFe::one()).iter().all(|&eq| eq),
                "add_affine_rhs requires rhs.z == 1 in every lane"
            );
            self.add_impl::<true>(rhs)
        }
        fn add_impl<const AFFINE_RHS: bool>(&self, rhs: &Self) -> Self {
            let a = self.y.subtract(&self.x).multiply(&rhs.y.subtract(&rhs.x));
            let b = self.y.add_loose(&self.x).multiply(&rhs.y.add_loose(&rhs.x));
            let c = self.t.multiply(&rhs.t).multiply(&WideFe::two_d());
            let d = if AFFINE_RHS {
                self.z.double_loose()
            } else {
                self.z.multiply(&rhs.z).double_loose()
            };
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
        /// Add the per-lane cached points selected for one digit.
        ///
        /// Transpose each cached field just before use; gathering all four needs
        /// 20 live ZMM registers and spills.
        #[inline(always)]
        fn add_cached_refs_assign(&mut self, points: &[&CachedPoint; LANES], compute_t: bool) {
            self.add_selected_cached_refs_assign(SelectedCachedRefs::Projective(points), compute_t);
        }
        /// Mixed addition with an affine cached point. The cached point has
        /// `Z = 1`, so `2*Z1*Z2` is just a doubling of the accumulator's `Z`.
        #[inline(always)]
        fn add_affine_cached_refs_assign(&mut self, points: &[&AffineCachedPoint; LANES]) {
            self.add_selected_cached_refs_assign(SelectedCachedRefs::Affine(points), true);
        }
        #[inline(never)]
        fn add_selected_cached_refs_assign(
            &mut self,
            points: SelectedCachedRefs<'_>,
            compute_t: bool,
        ) {
            // Loose products feed additive ops; use wide subtracts for limb0
            // values up to ~2^60.
            let a = self.y.subtract(&self.x).multiply_loose(&points.y_minus_x());
            let b = self.y.add_loose(&self.x).multiply_loose(&points.y_plus_x());
            let e = b.subtract_wide(&a);
            let h = b.add_loose(&a);
            let c = self.t.multiply_loose(&points.t2d());
            let d = match points.projective_z2() {
                Some(z2) => self.z.multiply_loose(&z2),
                None => self.z.double_loose(),
            };
            let f = d.subtract_wide(&c);
            let g = d.add_loose(&c);

            self.x = e.multiply(&f);
            self.t = if compute_t {
                e.multiply(&h)
            } else {
                WideFe::zero()
            };
            self.z = f.multiply(&g);
            self.y = g.multiply(&h);
        }
        #[cfg(test)]
        fn subtract(&self, rhs: &Self) -> Self {
            self.add(&rhs.negate())
        }
        /// Return whether `self - rhs` is killed by the Ed25519 cofactor.
        ///
        /// For `Q = self - rhs`, test `x(2Q)*y(2Q) == 0` via its numerator
        /// `E*H`, avoiding materialization of `Q` or `2Q`. Requires `rhs.z == 1`.
        fn subtract_affine_and_check_8_torsion(&self, rhs: &Self) -> [bool; LANES] {
            debug_assert!(
                rhs.z.equals_lanes(&WideFe::one()).iter().all(|&eq| eq),
                "ZIP-215 R subtraction requires affine rhs"
            );

            // Strongly-unified mixed subtraction.  Only X and Y are needed.
            let a = self.y.subtract(&self.x).multiply(&rhs.y.add_loose(&rhs.x));
            let b = self.y.add_loose(&self.x).multiply(&rhs.y.subtract(&rhs.x));
            let c = self.t.multiply(&rhs.t).multiply(&WideFe::two_d());
            let d = self.z.double_loose();
            let e = b.subtract(&a);
            let f = d.add_loose(&c);
            let g = d.subtract(&c);
            let h = b.add_loose(&a);
            let x = e.multiply(&f);
            let y = g.multiply(&h);

            // T(2Q) = E*H, where E = 2XY and H = -(X^2+Y^2).
            let xx = x.square_loose();
            let yy = y.square_loose();
            let double_e = x.add_loose(&y).square_loose().subtract_sum_wide(&xx, &yy);
            let double_h = WideFe::negate_sum_wide(&xx, &yy);
            double_e.multiply(&double_h).is_zero_lanes()
        }
        #[cfg(test)]
        fn negate(&self) -> Self {
            Self {
                x: self.x.negate(),
                y: self.y,
                z: self.z,
                t: self.t.negate(),
            }
        }
        fn double(&self) -> Self {
            self.double_impl::<true, false>()
        }
        fn double_affine(&self) -> Self {
            debug_assert!(
                self.z.equals_lanes(&WideFe::one()).iter().all(|&eq| eq),
                "double_affine requires z == 1 in every lane"
            );
            self.double_impl::<true, true>()
        }
        fn double_without_t(&self) -> Self {
            self.double_impl::<false, false>()
        }

        #[inline(never)]
        fn double4(&self) -> Self {
            let doubled = self
                .double_without_t()
                .double_without_t()
                .double_without_t();
            doubled.double()
        }
        fn double_impl<const COMPUTE_T: bool, const AFFINE_Z: bool>(&self) -> Self {
            // Loose squares feed additive ops; use wide subtract/negate for
            // limb0 values up to ~2^60.
            let a = self.x.square_loose();
            let b = self.y.square_loose();
            let z2 = if AFFINE_Z {
                WideFe::one()
            } else {
                self.z.square_loose()
            };
            let e = self
                .x
                .add_loose(&self.y)
                .square_loose()
                .subtract_sum_wide(&a, &b);
            let g = b.subtract_wide(&a);
            // `f = b - a - 2*z^2`; the factor of two rides along in the subtract.
            let f = b.subtract_sum_doubled_wide(&a, &z2);
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
        fn constant(limbs: [u64; LIMB_COUNT]) -> Self {
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
        // Broadcast the shared scalar/SIMD constants from `field.rs`.
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
    #[cfg(test)]
    mod simd_torsion_tests {
        use super::*;
        use rand::{RngCore, SeedableRng, rngs::StdRng};

        fn strict_square_n(x: &WideFe, n: usize) -> WideFe {
            let mut out = *x;
            for _ in 0..n {
                out = out.square();
            }
            out
        }

        fn wide_from_rows(rows: [[u64; LANES]; LIMB_COUNT]) -> WideFe {
            WideFe {
                limbs: core::array::from_fn(|i| loadu(rows[i])),
            }
        }

        fn assert_wide_matches(
            actual: WideFe,
            expected: &[crate::field::Fe51; LANES],
            operation: &str,
            round: usize,
        ) {
            for (lane, (actual, expected)) in
                actual.to_fields().iter().zip(expected.iter()).enumerate()
            {
                assert!(
                    actual.equals(expected),
                    "{operation} lane {lane} diverged at round {round}"
                );
            }
        }

        /// Cross-check vectorized canonical predicates against scalar references.
        fn check_canonical(rows: [[u64; LANES]; LIMB_COUNT]) {
            let wide = wide_from_rows(rows);
            let canonical = wide.canonical();
            let mut canonical_rows = [[0u64; LANES]; LIMB_COUNT];
            for (limb, row) in canonical_rows.iter_mut().enumerate() {
                storeu(canonical.limbs[limb], row);
            }
            let is_zero = wide.is_zero_lanes();
            let is_odd = wide.is_odd_lanes();

            for lane in 0..LANES {
                let input: [u64; LIMB_COUNT] = core::array::from_fn(|limb| rows[limb][lane]);
                // Limb comparison pins the representation, not just the residue.
                let expected = crate::field::Fe51::from_limbs(input).reduced_limbs();
                let actual: [u64; LIMB_COUNT] =
                    core::array::from_fn(|limb| canonical_rows[limb][lane]);
                assert_eq!(
                    actual, expected,
                    "lane {lane} diverged from the field.rs Fe51 reference"
                );
                assert_eq!(
                    is_zero[lane],
                    expected == [0u64; LIMB_COUNT],
                    "is_zero_lanes lane {lane}"
                );
                assert_eq!(
                    is_odd[lane],
                    (expected[0] & 1) != 0,
                    "is_odd_lanes lane {lane}"
                );
            }
        }

        #[test]
        fn canonical_matches_scalar_reference() {
            let zero = [0u64; LIMB_COUNT];
            let p = crate::field::P_LIMBS;
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
            let max_limbs = [(1u64 << 52) - 1; LIMB_COUNT];
            let hand_picked = [zero, p, p_minus_1, p_plus_1, max_limbs];

            let mut rng = StdRng::seed_from_u64(0xbb67_ae85_84ca_a73b);

            let mut rows = [[0u64; LANES]; LIMB_COUNT];
            for lane in 0..LANES {
                let limbs = if lane < hand_picked.len() {
                    hand_picked[lane]
                } else {
                    core::array::from_fn(|_| rng.next_u64() & ((1u64 << 52) - 1))
                };
                for limb in 0..5 {
                    rows[limb][lane] = limbs[limb];
                }
            }
            check_canonical(rows);

            let mut rng = StdRng::seed_from_u64(0x9e37_79b9_7f4a_7c15);
            for _ in 0..512 {
                let mut rows = [[0u64; LANES]; LIMB_COUNT];
                for row in &mut rows {
                    for value in row {
                        *value = rng.next_u64() & ((1u64 << 52) - 1);
                    }
                }
                check_canonical(rows);
            }
        }

        #[test]
        fn wide_field_operations_match_scalar_reference() {
            const LOOSE_MASK: u64 = (1u64 << 52) - 1;

            let mut rng = StdRng::seed_from_u64(0x510e_527f_ade6_82d1);
            for round in 0..512 {
                let mut random_fields = || {
                    core::array::from_fn(|_| {
                        crate::field::Fe51::from_limbs(core::array::from_fn(|_| {
                            rng.next_u64() & LOOSE_MASK
                        }))
                    })
                };
                let a_fields: [crate::field::Fe51; LANES] = random_fields();
                let b_fields: [crate::field::Fe51; LANES] = random_fields();
                let c_fields: [crate::field::Fe51; LANES] = random_fields();
                let a = WideFe::from_fields(&a_fields);
                let b = WideFe::from_fields(&b_fields);
                let c = WideFe::from_fields(&c_fields);

                let add = core::array::from_fn(|lane| a_fields[lane].add(&b_fields[lane]));
                let subtract =
                    core::array::from_fn(|lane| a_fields[lane].subtract(&b_fields[lane]));
                let multiply =
                    core::array::from_fn(|lane| a_fields[lane].multiply(&b_fields[lane]));
                let square = core::array::from_fn(|lane| a_fields[lane].square());
                assert_wide_matches(a.add(&b), &add, "add", round);
                assert_wide_matches(a.add_loose(&b), &add, "add_loose", round);
                assert_wide_matches(a.subtract(&b), &subtract, "subtract", round);
                assert_wide_matches(a.multiply(&b), &multiply, "multiply", round);
                assert_wide_matches(a.multiply_loose(&b), &multiply, "multiply_loose", round);
                assert_wide_matches(a.square(), &square, "square", round);
                assert_wide_matches(a.square_loose(), &square, "square_loose", round);

                let ab = a.multiply_loose(&b);
                let bc = b.multiply_loose(&c);
                let cc = c.square_loose();
                let bc_fields: [crate::field::Fe51; LANES] =
                    core::array::from_fn(|lane| b_fields[lane].multiply(&c_fields[lane]));
                let cc_fields: [crate::field::Fe51; LANES] =
                    core::array::from_fn(|lane| c_fields[lane].square());
                let subtract_wide =
                    core::array::from_fn(|lane| multiply[lane].subtract(&bc_fields[lane]));
                let subtract_sum = core::array::from_fn(|lane| {
                    multiply[lane]
                        .subtract(&bc_fields[lane])
                        .subtract(&cc_fields[lane])
                });
                let subtract_sum_doubled = core::array::from_fn(|lane| {
                    multiply[lane]
                        .subtract(&bc_fields[lane])
                        .subtract(&cc_fields[lane].add(&cc_fields[lane]))
                });
                let negate_sum = core::array::from_fn(|lane| {
                    crate::field::Fe51::zero()
                        .subtract(&bc_fields[lane])
                        .subtract(&cc_fields[lane])
                });
                assert_wide_matches(
                    ab.subtract_wide(&bc),
                    &subtract_wide,
                    "subtract_wide",
                    round,
                );
                assert_wide_matches(
                    ab.subtract_sum_wide(&bc, &cc),
                    &subtract_sum,
                    "subtract_sum_wide",
                    round,
                );
                assert_wide_matches(
                    ab.subtract_sum_doubled_wide(&bc, &cc),
                    &subtract_sum_doubled,
                    "subtract_sum_doubled_wide",
                    round,
                );
                assert_wide_matches(
                    WideFe::negate_sum_wide(&bc, &cc),
                    &negate_sum,
                    "negate_sum_wide",
                    round,
                );
            }

            let near_max = core::array::from_fn(|limb| {
                core::array::from_fn(|lane| {
                    if limb == 0 {
                        (1u64 << 60) - 1 - lane as u64
                    } else {
                        LIMB_MASK - lane as u64
                    }
                })
            });
            let fields: [crate::field::Fe51; LANES] = core::array::from_fn(|lane| {
                crate::field::Fe51::from_limbs(core::array::from_fn(|limb| near_max[limb][lane]))
            });
            let wide = wide_from_rows(near_max);
            let zero = core::array::from_fn(|lane| fields[lane].subtract(&fields[lane]));
            let negated =
                core::array::from_fn(|lane| crate::field::Fe51::zero().subtract(&fields[lane]));
            let double_negated = core::array::from_fn(|lane| negated[lane].subtract(&fields[lane]));
            let square = core::array::from_fn(|lane| fields[lane].square());
            assert_wide_matches(wide.subtract_wide(&wide), &zero, "wide-bound subtract", 0);
            assert_wide_matches(
                wide.subtract_sum_wide(&wide, &wide),
                &negated,
                "wide-bound subtract-sum",
                0,
            );
            assert_wide_matches(
                wide.subtract_sum_doubled_wide(&wide, &wide),
                &double_negated,
                "wide-bound subtract-sum-doubled",
                0,
            );
            assert_wide_matches(
                WideFe::negate_sum_wide(&wide, &wide),
                &double_negated,
                "wide-bound negate-sum",
                0,
            );
            assert_wide_matches(wide.square(), &square, "wide-bound square", 0);
            assert_wide_matches(wide.square_loose(), &square, "wide-bound square-loose", 0);
        }

        #[test]
        fn square_repeat_variants_match_strict_reference() {
            // Check every exponent-chain count plus the N=0/1 boundaries.
            let a = WideFe::constant(crate::field::D_LIMBS);
            let b = WideFe::constant(crate::field::SQRT_M1_LIMBS);
            macro_rules! check {
                ($n:literal) => {
                    assert!(
                        WideFe::square_repeat::<$n>(&a)
                            .equals_lanes(&strict_square_n(&a, $n))
                            .iter()
                            .all(|&v| v),
                        "square_repeat::<{}> diverged for a",
                        $n
                    );
                    assert!(
                        WideFe::square_repeat::<$n>(&b)
                            .equals_lanes(&strict_square_n(&b, $n))
                            .iter()
                            .all(|&v| v),
                        "square_repeat::<{}> diverged for b",
                        $n
                    );
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
        fn pow_variants_match_scalar_reference() {
            let mut rng = StdRng::seed_from_u64(0x3c6e_f372_fe94_f82b);

            for round in 0..200 {
                let mut random_fields = || {
                    core::array::from_fn(|_| {
                        let limbs: [u64; LIMB_COUNT] =
                            core::array::from_fn(|_| rng.next_u64() & LIMB_MASK);
                        crate::field::Fe51::from_limbs(limbs)
                    })
                };
                let fields_a: [crate::field::Fe51; LANES] = random_fields();
                let fields_b: [crate::field::Fe51; LANES] = random_fields();
                let a = WideFe::from_fields(&fields_a);
                let b = WideFe::from_fields(&fields_b);
                let sequential_a = a.pow_p_minus_5_over_8().to_fields();
                let sequential_b = b.pow_p_minus_5_over_8().to_fields();
                let (paired_a, paired_b) = WideFe::pow_p_minus_5_over_8_x2(&a, &b);
                let paired_a = paired_a.to_fields();
                let paired_b = paired_b.to_fields();

                for lane in 0..LANES {
                    let expected_a = fields_a[lane].pow_p_minus_5_over_8();
                    let expected_b = fields_b[lane].pow_p_minus_5_over_8();
                    assert!(
                        expected_a.equals(&sequential_a[lane])
                            && expected_a.equals(&paired_a[lane]),
                        "a lane {lane} diverged at round {round}"
                    );
                    assert!(
                        expected_b.equals(&sequential_b[lane])
                            && expected_b.equals(&paired_b[lane]),
                        "b lane {lane} diverged at round {round}"
                    );
                }
            }
        }

        #[test]
        fn wide_decompression_matches_scalar_reference() {
            let mut rng = StdRng::seed_from_u64(0x1f83_d9ab_fb41_bd6b);

            for round in 0..512 {
                let encodings: [[u8; POINT_ENCODING_LEN]; LANES] = core::array::from_fn(|_| {
                    let mut encoding = [0u8; POINT_ENCODING_LEN];
                    rng.fill_bytes(&mut encoding);
                    encoding
                });
                let (wide, mask) = decompress_points_wide(&encodings);
                let points = wide.to_points();

                for lane in 0..LANES {
                    let expected = EdwardsPoint::decompress(&encodings[lane]);
                    assert_eq!(
                        (mask & (1 << lane)) != 0,
                        expected.is_some(),
                        "validity mask lane {lane} diverged at round {round}"
                    );
                    if let Some(expected) = expected {
                        assert_eq!(
                            points[lane].compress(),
                            expected.compress(),
                            "decoded point lane {lane} diverged at round {round}"
                        );
                    }
                }
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
        fn wide_torsion_operations_match_scalar() {
            let p = ord8a();
            let scalar_doubled = p.double();
            let wide = WidePoint::from_points(&core::array::from_fn(|_| p.clone()));
            let wide_doubled = wide.double().to_points();
            assert_eq!(
                wide_doubled[0].compress(),
                scalar_doubled.compress(),
                "wide double diverges from scalar on an order-8 point"
            );

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

            let bytes = p.compress();
            let (wide, mask) = decompress_points_wide(&[bytes; LANES]);
            assert_eq!(mask, 0xff, "wide decode must succeed");
            let wide_pts = wide.to_points();
            assert_eq!(
                wide_pts[0].compress(),
                bytes,
                "wide decompress diverges from scalar on an order-8 point"
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
            let combined = mul_base_minus_public::<true>(&base_table, &prepared);
            let pts = combined.to_points();
            assert_eq!(
                pts[0].compress(),
                id.compress(),
                "sB - kA for s=0, A=identity must be identity"
            );
        }
    }
}
