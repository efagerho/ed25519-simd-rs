pub(crate) mod avx512ifma {
    use crate::batch::{PUBLIC_KEY_LEN, PreparedChunk, R_ENCODING_LEN};
    #[cfg(test)]
    use crate::edwards::BasepointTable;
    use crate::edwards::{
        AffineCachedPoint, BASEPOINT_COMPRESSED, BASEPOINT_TABLE_SIZE, BasepointTableEntries,
        CachedPoint, POINT_ENCODING_LEN, PointTable, select_signed_affine_cached_ref,
    };
    use crate::field::{Fe51, LIMB_COUNT};
    use crate::scalar::Radix16;
    use std::arch::x86_64::*;

    const LANES: usize = crate::batch::SIMD_LANES;
    // These intrinsics hard-code eight lanes; reject a changed `SIMD_LANES`.
    const _: () = assert!(LANES == 8, "avx512ifma assumes exactly 8 SIMD lanes");
    const LIMB_MASK: u64 = (1u64 << 51) - 1;
    pub(crate) struct WideRPoint {
        point: WidePoint,
        x_zero_mask: Option<u8>,
    }

    /// An uncompressed Dalek verification result waiting to be compared with
    /// the signature's encoded R point.
    pub(crate) struct DalekCandidate(WidePoint);

    impl WideRPoint {
        /// Dalek-invalid negative-zero lanes.
        pub(crate) fn x_zero_lanes(&self) -> [bool; LANES] {
            let mask = self
                .x_zero_mask
                .expect("x-zero lanes were not tracked for this decode");
            mask_to_lanes(mask)
        }
    }

    /// Decompress one SIMD chunk of `R` points and return a per-lane validity mask.
    pub(crate) fn decompress_r_points(r_bytes: &[[u8; R_ENCODING_LEN]; LANES]) -> (WideRPoint, u8) {
        let (point, mask) = decompress_points_wide(r_bytes);
        (
            WideRPoint {
                point,
                x_zero_mask: None,
            },
            mask,
        )
    }

    /// Decode keys and `R` together, interleaving their inverse-square-root chains.
    #[inline(never)]
    pub(crate) fn decode_keys_and_decompress_r(
        keys: &[[u8; PUBLIC_KEY_LEN]; LANES],
        r_bytes: &[[u8; R_ENCODING_LEN]; LANES],
        dalek: bool,
        key_tables: &mut [Option<PointTable>; LANES],
    ) -> (u8, WideRPoint, u8) {
        let ((kp, kmask), (rp, rmask, x_zero_mask)) =
            decompress_two_point_chunks_wide(keys, r_bytes, dalek);
        build_tables_from_point(kp, key_tables);
        (
            kmask,
            WideRPoint {
                point: rp,
                x_zero_mask,
            },
            rmask,
        )
    }

    /// Decode one public key and build its cached table with the SIMD field
    /// implementation. All lanes contain the same public input; only lane zero
    /// is materialized into the returned table.
    pub(crate) fn decode_public_key_table(encoded: &[u8; PUBLIC_KEY_LEN]) -> Option<PointTable> {
        let (point, mask) = cold_decompress_points_wide(&[*encoded; LANES]);
        if mask & 1 == 0 {
            return None;
        }
        Some(build_lane0_table_from_point(point))
    }

    /// Construct the affine fixed-base table as 17 vectors whose lanes hold
    /// consecutive multiples. Montgomery batch inversion across those vectors
    /// normalizes all 136 points with one eight-lane inversion.
    pub(crate) fn build_basepoint_table_entries() -> Box<BasepointTableEntries> {
        let points = build_projective_basepoint_blocks();
        let inverse_z = batch_invert_basepoint_zs(&points);
        affine_basepoint_entries(&points, &inverse_z)
    }

    #[inline(never)]
    fn build_projective_basepoint_blocks() -> Vec<WidePoint> {
        const BLOCKS: usize = BASEPOINT_TABLE_SIZE / LANES;
        const {
            assert!(BASEPOINT_TABLE_SIZE.is_multiple_of(LANES));
        }

        let (basepoint, mask) = cold_decompress_points_wide(&[BASEPOINT_COMPRESSED; LANES]);
        assert_eq!(mask, u8::MAX, "the standard basepoint must decompress");

        let (mut block, p8) = first_basepoint_block(basepoint);
        let mut points = Vec::with_capacity(BLOCKS);
        for i in 0..BLOCKS {
            points.push(block);
            if i + 1 < BLOCKS {
                block = block.cold_add(&p8);
            }
        }
        points
    }

    /// Build duplicated vectors B..8B, then transpose lane zero from each
    /// into one vector `[B, 2B, ..., 8B]`. Keeping this stage out of the caller
    /// bounds debug-build stack use despite the large SIMD point type.
    #[inline(never)]
    fn first_basepoint_block(basepoint: WidePoint) -> (WidePoint, WidePoint) {
        let p2 = basepoint.cold_double_from_affine();
        let p3 = p2.add_affine_rhs(&basepoint);
        let p4 = p2.double();
        let p5 = p4.add_affine_rhs(&basepoint);
        let p6 = p3.double();
        let p7 = p4.cold_add(&p3);
        let p8 = p4.double();
        (
            WidePoint::from_lane0_points(&[basepoint, p2, p3, p4, p5, p6, p7, p8]),
            p8,
        )
    }

    #[inline(never)]
    fn batch_invert_basepoint_zs(points: &[WidePoint]) -> Vec<WideFe> {
        let mut inverse_z = Vec::with_capacity(points.len());
        let mut product = WideFe::one();
        for point in points {
            inverse_z.push(product);
            product = product.multiply(&point.z);
        }
        let mut inverse_accumulator = product.cold_invert();
        for i in (0..points.len()).rev() {
            inverse_z[i] = inverse_z[i].multiply(&inverse_accumulator);
            inverse_accumulator = inverse_accumulator.multiply(&points[i].z);
        }
        inverse_z
    }

    #[inline(never)]
    fn affine_basepoint_entries(
        points: &[WidePoint],
        inverse_z: &[WideFe],
    ) -> Box<BasepointTableEntries> {
        let two_d = WideFe::two_d();
        let mut positive = Vec::with_capacity(BASEPOINT_TABLE_SIZE);
        let mut negative = Vec::with_capacity(BASEPOINT_TABLE_SIZE);
        for (point, zinv) in points.iter().zip(inverse_z.iter()) {
            let x = point.x.multiply(zinv);
            let y = point.y.multiply(zinv);
            let y_plus_x = y.add(&x).to_fields_loose();
            let y_minus_x = y.subtract(&x).to_fields_loose();
            let t2d = x.multiply(&y).multiply(&two_d);
            let positive_t2d = t2d.to_fields_loose();
            let negative_t2d = t2d.negate().to_fields_loose();

            for lane in 0..LANES {
                positive.push(AffineCachedPoint::from_fields(
                    y_plus_x[lane],
                    y_minus_x[lane],
                    positive_t2d[lane],
                ));
                negative.push(AffineCachedPoint::from_fields(
                    y_minus_x[lane],
                    y_plus_x[lane],
                    negative_t2d[lane],
                ));
            }
        }

        // Signed layout: -136B..-B, identity, B..136B.
        let mut entries = Vec::with_capacity(2 * BASEPOINT_TABLE_SIZE + 1);
        entries.extend(negative.into_iter().rev());
        entries.push(AffineCachedPoint::identity());
        entries.extend(positive);
        entries
            .into_boxed_slice()
            .try_into()
            .unwrap_or_else(|_| unreachable!("basepoint table length is fixed"))
    }

    /// Build the per-lane radix-16 cached tables from an already-decompressed
    /// SIMD point.
    /// Every slot is filled, including lanes whose decode failed; the caller
    /// discards those by mask.
    fn build_tables_from_point(p: WidePoint, tables: &mut [Option<PointTable>; LANES]) {
        for table in tables.iter_mut() {
            // SAFETY: the calls below fill positive and negative 1..=8 before
            // this function returns or any table can be selected.
            *table = Some(unsafe { PointTable::decode_destination() });
        }

        write_cached_multiple(1, &p, tables);

        // Build P..8P as a depth-4 tree, writing each point immediately.
        let p2 = p.double_from_affine();
        write_cached_multiple(2, &p2, tables);

        let p3 = p2.add_affine_rhs(&p);
        write_cached_multiple(3, &p3, tables);

        let p4 = p2.double();
        write_cached_multiple(4, &p4, tables);

        write_cached_multiple(5, &p4.add_affine_rhs(&p), tables);
        write_cached_multiple(6, &p3.double(), tables);
        write_cached_multiple(7, &p4.add(&p3), tables);
        write_cached_multiple(8, &p4.double(), tables);
    }

    fn build_lane0_table_from_point(p: WidePoint) -> PointTable {
        let mut table = PointTable::cold_identity();
        write_cached_multiple_lane0(1, &p, &mut table);

        let p2 = p.cold_double_from_affine();
        write_cached_multiple_lane0(2, &p2, &mut table);

        let p3 = p2.add_affine_rhs(&p);
        write_cached_multiple_lane0(3, &p3, &mut table);

        let p4 = p2.double();
        write_cached_multiple_lane0(4, &p4, &mut table);
        write_cached_multiple_lane0(5, &p4.add_affine_rhs(&p), &mut table);
        write_cached_multiple_lane0(6, &p3.double(), &mut table);
        write_cached_multiple_lane0(7, &p4.cold_add(&p3), &mut table);
        write_cached_multiple_lane0(8, &p4.double(), &mut table);
        table
    }

    fn write_cached_multiple_lane0(multiple: usize, point: &WidePoint, table: &mut PointTable) {
        let y_plus_x = point.y.add(&point.x).lane0();
        let y_minus_x = point.y.subtract(&point.x).lane0();
        let z2 = point.z.double().lane0();
        let t2d = point.t.multiply(&WideFe::two_d());
        let positive = CachedPoint::from_fields(y_plus_x, y_minus_x, z2, t2d.lane0());
        let negative = CachedPoint::from_fields(y_minus_x, y_plus_x, z2, t2d.negate().lane0());
        table.set_multiple(multiple, positive, negative);
    }

    #[inline(never)]
    fn write_cached_multiple(
        multiple: usize,
        point: &WidePoint,
        tables: &mut [Option<PointTable>; LANES],
    ) {
        let two_d = WideFe::two_d();
        type LaneFields = [Fe51; LANES];
        let fields: (LaneFields, LaneFields, LaneFields, LaneFields, LaneFields) = {
            let ypx = point.y.add(&point.x);
            let ymx = point.y.subtract(&point.x);
            let z2 = point.z.double();
            let t2d = point.t.multiply(&two_d);
            let neg_t2d = t2d.negate();
            (
                ypx.to_fields_loose(),
                ymx.to_fields_loose(),
                z2.to_fields_loose(),
                t2d.to_fields_loose(),
                neg_t2d.to_fields_loose(),
            )
        };

        let (ypx, ymx, z2, t2d, neg_t2d) = fields;
        for lane in 0..LANES {
            let positive = CachedPoint::from_fields(ypx[lane], ymx[lane], z2[lane], t2d[lane]);
            let negative = CachedPoint::from_fields(ymx[lane], ypx[lane], z2[lane], neg_t2d[lane]);
            tables[lane]
                .as_mut()
                .expect("table destinations were initialized")
                .set_multiple(multiple, positive, negative);
        }
    }

    // ZIP-215 cofactored verification: [8](sB - kA - R) == identity.
    pub(crate) fn verify_prepared_zip215(
        prepared: &PreparedChunk<'_>,
        r: &WideRPoint,
        base_table: &BasepointTableEntries,
    ) -> [bool; LANES] {
        let combined = mul_s_base_minus_k_public::<true>(base_table, prepared);
        combined.subtract_affine_and_check_8_torsion(&r.point)
    }

    pub(crate) fn prepare_dalek_candidate(
        prepared: &PreparedChunk<'_>,
        base_table: &BasepointTableEntries,
    ) -> DalekCandidate {
        DalekCandidate(mul_s_base_minus_k_public::<false>(base_table, prepared))
    }

    pub(crate) fn verify_prepared_dalek_encoded_r(
        prepared: &PreparedChunk<'_>,
        r_bytes: &[[u8; R_ENCODING_LEN]; LANES],
        base_table: &BasepointTableEntries,
    ) -> [bool; LANES] {
        let combined = mul_s_base_minus_k_public::<false>(base_table, prepared);
        let recomputed = combined.compress();
        core::array::from_fn(|lane| recomputed[lane] == r_bytes[lane])
    }

    pub(crate) fn verify_dalek_candidate(
        candidate: &DalekCandidate,
        r_bytes: &[[u8; R_ENCODING_LEN]; LANES],
    ) -> [bool; LANES] {
        let recomputed = candidate.0.compress();
        core::array::from_fn(|lane| recomputed[lane] == r_bytes[lane])
    }

    /// Normalize two chunks with one field inversion. The extra three field
    /// multiplications implement Montgomery's trick: invert `z0*z1`, then
    /// recover each individual reciprocal from the shared result.
    pub(crate) fn verify_dalek_candidate_pair(
        first: &DalekCandidate,
        first_r_bytes: &[[u8; R_ENCODING_LEN]; LANES],
        second: &DalekCandidate,
        second_r_bytes: &[[u8; R_ENCODING_LEN]; LANES],
    ) -> ([bool; LANES], [bool; LANES]) {
        let (first_encoding, second_encoding) = WidePoint::compress_pair(&first.0, &second.0);
        (
            core::array::from_fn(|lane| first_encoding[lane] == first_r_bytes[lane]),
            core::array::from_fn(|lane| second_encoding[lane] == second_r_bytes[lane]),
        )
    }

    pub(crate) fn verify_prepared_dalek_decompressed_r(
        prepared: &PreparedChunk<'_>,
        r: &WideRPoint,
        base_table: &BasepointTableEntries,
    ) -> [bool; LANES] {
        let combined = mul_s_base_minus_k_public::<false>(base_table, prepared);
        combined.equals_affine_lanes(&r.point)
    }

    /// Decompression state before the inverse-square-root exponentiation.
    struct DecompressSetup {
        u: WideFe,
        v: WideFe,
        uv: WideFe, // raised to (p-5)/8
        y: WideFe,
        x_sign_mask: u8,
    }

    fn decompress_setup(bytes: &[[u8; POINT_ENCODING_LEN]; LANES]) -> DecompressSetup {
        let mut y_fields = core::array::from_fn(|_| Fe51::zero());
        let mut x_sign_mask = 0u8;

        for (lane, byte_arr) in bytes.iter().enumerate() {
            x_sign_mask |= (byte_arr[31] >> 7) << lane;
            let mut y_bytes = *byte_arr;
            y_bytes[31] &= 0x7f;
            // ZIP-215/Dalek decoding treats y modulo p.
            y_fields[lane] = Fe51::from_bytes_unchecked(&y_bytes);
        }

        let y = WideFe::from_fields(&y_fields);
        let yy = y.square();
        let u = yy.subtract(&WideFe::one());
        let v = WideFe::one().add(&WideFe::d().multiply(&yy));
        let uv = u.multiply(&v);
        DecompressSetup {
            u,
            v,
            uv,
            y,
            x_sign_mask,
        }
    }

    fn decompress_finish<const COMPUTE_T: bool, const TRACK_X_ZERO: bool>(
        s: DecompressSetup,
        pow: WideFe,
    ) -> (WidePoint, u8, Option<u8>) {
        let mut x = s.u.multiply(&pow);

        let vx2 = s.v.multiply(&x.square());
        let primary_root_mask = vx2.equals_mask(&s.u);

        let x_alt = x.multiply(&WideFe::sqrt_m1());
        // The alternate root is valid iff the existing `vx2` equals `-u`.
        let alternate_root_mask = vx2.add_loose(&s.u).is_zero_mask();

        let use_alternate_root_mask = !primary_root_mask & alternate_root_mask;
        let valid_mask = primary_root_mask | alternate_root_mask;

        x = x.blend(use_alternate_root_mask, &x_alt);

        // Points outside `valid_mask` are garbage.
        let (x_odd_mask, x_zero_mask) = if TRACK_X_ZERO {
            let (odd, zero) = x.odd_and_zero_masks();
            (odd, Some(zero))
        } else {
            (x.is_odd_mask(), None)
        };
        let x_neg = x.negate();
        let negate_mask = x_odd_mask ^ s.x_sign_mask;
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
        let pow = s.uv.pow_p_minus_5_over_8();
        let (point, mask, _) = decompress_finish::<true, false>(s, pow);
        (point, mask)
    }

    /// Initialization-only decompression, kept distinct so setup work cannot
    /// change inlining in verification's single-chunk decompression path.
    #[inline(never)]
    fn cold_decompress_points_wide(bytes: &[[u8; POINT_ENCODING_LEN]; LANES]) -> (WidePoint, u8) {
        let s = decompress_setup(bytes);
        let pow = s.uv.cold_pow_p_minus_5_over_8();
        let (point, mask, _) = decompress_finish::<true, false>(s, pow);
        (point, mask)
    }

    /// Decompress two independent SIMD chunks, interleaving the two
    /// inverse-square-root chains so each fills the other's IFMA latency gaps.
    fn decompress_two_point_chunks_wide(
        a_bytes: &[[u8; POINT_ENCODING_LEN]; LANES],
        b_bytes: &[[u8; POINT_ENCODING_LEN]; LANES],
        minimize_b_for_dalek: bool,
    ) -> ((WidePoint, u8), (WidePoint, u8, Option<u8>)) {
        let sa = decompress_setup(a_bytes);
        let sb = decompress_setup(b_bytes);
        let (pa, pb) = WideFe::pow_p_minus_5_over_8_x2(&sa.uv, &sb.uv);
        let (a, a_mask, _) = decompress_finish::<true, false>(sa, pa);
        let b = if minimize_b_for_dalek {
            decompress_finish::<false, true>(sb, pb)
        } else {
            decompress_finish::<true, false>(sb, pb)
        };
        ((a, a_mask), b)
    }
    // Only ZIP-215's final torsion subtraction needs T.
    fn mul_s_base_minus_k_public<const NEED_T: bool>(
        base_table: &BasepointTableEntries,
        prepared: &PreparedChunk<'_>,
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
        acc.double_four_times_assign();
        add_base_pair_digit(&mut acc, base_table, s_digits, 31);
        subtract_public_key_digit_before_double(&mut acc, public_key_tables, k_digits, 62);

        // These public-key additions feed doublings, which do not use `T`.
        for pair in (1..31).rev() {
            acc.double_four_times_assign();
            subtract_public_key_digit_before_double(
                &mut acc,
                public_key_tables,
                k_digits,
                pair * 2 + 1,
            );

            acc.double_four_times_assign();
            add_base_pair_digit(&mut acc, base_table, s_digits, pair);
            subtract_public_key_digit_before_double(
                &mut acc,
                public_key_tables,
                k_digits,
                pair * 2,
            );
        }

        acc.double_four_times_assign();
        subtract_public_key_digit_before_double(&mut acc, public_key_tables, k_digits, 1);
        acc.double_four_times_assign();
        add_base_pair_digit(&mut acc, base_table, s_digits, 0);
        if NEED_T {
            subtract_public_key_digit(&mut acc, public_key_tables, k_digits, 0);
        } else {
            subtract_public_key_digit_before_double(&mut acc, public_key_tables, k_digits, 0);
        }
        acc
    }

    #[inline]
    fn add_base_pair_digit(
        acc: &mut WidePoint,
        base_table: &BasepointTableEntries,
        s_digits: &[Radix16; LANES],
        pair: usize,
    ) {
        let selected: [_; LANES] = core::array::from_fn(|lane| {
            select_signed_affine_cached_ref(base_table, base_pair_digit(&s_digits[lane], pair))
        });
        acc.add_affine_cached_refs_assign(&selected);
    }

    #[inline]
    fn subtract_public_key_digit(
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
    fn subtract_public_key_digit_before_double(
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
            Self::from_limbs_per_lane(|lane| fields[lane].loose_limbs())
        }
        fn from_field_refs(fields: &[&Fe51; LANES]) -> Self {
            Self::from_limbs_per_lane(|lane| fields[lane].loose_limbs())
        }
        fn lane0(self) -> Fe51 {
            unsafe {
                Fe51::from_limbs_unchecked(core::array::from_fn(|i| {
                    _mm_cvtsi128_si64(_mm512_castsi512_si128(self.limbs[i])) as u64
                }))
            }
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
        // loose limb0 can reach < 2^60, so those callers use `subtract_loose`.
        //
        // Note the suffix convention split: on `multiply`/`square`/`add`,
        // `_loose` marks a looser *result*; on the subtraction family below it
        // marks looser *operands* (the results are equally loose either way).
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

        // `self + 2048*p - rhs`. These loose-input forms use a 2048*p bias,
        // enough for two loose subtrahends (limb0 < 2^60); `subtract`'s 4*p is not.
        fn subtract_loose(&self, rhs: &Self) -> Self {
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
        fn subtract_loose_sum(&self, lhs: &Self, rhs: &Self) -> Self {
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

        // Fold `2*rhs` into the loose-input subtraction to avoid a carry pass.
        fn subtract_loose_sum_with_doubled_rhs(&self, lhs: &Self, rhs: &Self) -> Self {
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
        fn negate_loose_sum(lhs: &Self, rhs: &Self) -> Self {
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

        #[inline(never)]
        fn cold_pow_p_minus_5_over_8(&self) -> Self {
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
        #[inline(never)]
        fn cold_invert(&self) -> Self {
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
            mask_to_lanes(self.equals_mask(rhs))
        }
        fn equals_mask(self, rhs: &Self) -> u8 {
            self.subtract(rhs).is_zero_mask()
        }
        fn is_zero_lanes(self) -> [bool; LANES] {
            mask_to_lanes(self.is_zero_mask())
        }
        fn is_zero_mask(self) -> u8 {
            self.canonical().canonical_zero_mask()
        }
        /// Zero mask of an already-canonicalized value.
        #[inline(always)]
        fn canonical_zero_mask(&self) -> u8 {
            unsafe {
                let zero = _mm512_setzero_si512();
                _mm512_cmpeq_epu64_mask(self.limbs[0], zero)
                    & _mm512_cmpeq_epu64_mask(self.limbs[1], zero)
                    & _mm512_cmpeq_epu64_mask(self.limbs[2], zero)
                    & _mm512_cmpeq_epu64_mask(self.limbs[3], zero)
                    & _mm512_cmpeq_epu64_mask(self.limbs[4], zero)
            }
        }
        #[cfg(test)]
        fn is_odd_lanes(self) -> [bool; LANES] {
            mask_to_lanes(self.is_odd_mask())
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
                _mm512_test_epi64_mask(c.limbs[0], one)
            }
        }
        /// Return parity and zero masks from one canonicalization.
        fn odd_and_zero_masks(self) -> (u8, u8) {
            unsafe {
                let c = self.canonical();
                let one = _mm512_set1_epi64(1);
                (
                    _mm512_test_epi64_mask(c.limbs[0], one),
                    c.canonical_zero_mask(),
                )
            }
        }
        /// Vectorized `Fe51::canonical`; bounded high limbs reduce `>= p` to a
        /// high-limb check and limb-0 threshold.
        fn canonical(&self) -> Self {
            unsafe {
                let reduced = Self::carry_reduce_twice(self.limbs);
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
        fn carry_reduce_twice(h: [__m512i; LIMB_COUNT]) -> Self {
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
        /// Pack lane zero from eight duplicated points into independent lanes.
        fn from_lane0_points(points: &[Self; LANES]) -> Self {
            let field = |pick: fn(&Self) -> WideFe| {
                WideFe::from_fields(&core::array::from_fn(|lane| pick(&points[lane]).lane0()))
            };
            Self {
                x: field(|point| point.x),
                y: field(|point| point.y),
                z: field(|point| point.z),
                t: field(|point| point.t),
            }
        }

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
            self.compress_with_z_inverse(&zinv)
        }
        fn compress_pair(
            first: &Self,
            second: &Self,
        ) -> (
            [[u8; POINT_ENCODING_LEN]; LANES],
            [[u8; POINT_ENCODING_LEN]; LANES],
        ) {
            let product_inverse = first.z.multiply(&second.z).invert();
            let first_z_inverse = product_inverse.multiply(&second.z);
            let second_z_inverse = product_inverse.multiply(&first.z);
            (
                first.compress_with_z_inverse(&first_z_inverse),
                second.compress_with_z_inverse(&second_z_inverse),
            )
        }
        fn compress_with_z_inverse(&self, zinv: &WideFe) -> [[u8; POINT_ENCODING_LEN]; LANES] {
            let x = self.x.multiply(zinv);
            let y = self.y.multiply(zinv);
            let x_odd_mask = x.is_odd_mask();
            let mut bytes = y.to_bytes_lanes();
            for (lane, encoding) in bytes.iter_mut().enumerate() {
                encoding[31] |= ((x_odd_mask >> lane) & 1) << 7;
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

        /// Initialization-only copy of projective addition. Keeping its call
        /// sites separate preserves the hot table builder's inlining choices.
        #[inline(never)]
        fn cold_add(&self, rhs: &Self) -> Self {
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
            // Loose products feed additive ops; use loose-input subtracts for limb0
            // values up to ~2^60.
            let a = self.y.subtract(&self.x).multiply_loose(&points.y_minus_x());
            let b = self.y.add_loose(&self.x).multiply_loose(&points.y_plus_x());
            let e = b.subtract_loose(&a);
            let h = b.add_loose(&a);
            let c = self.t.multiply_loose(&points.t2d());
            let d = match points.projective_z2() {
                Some(z2) => self.z.multiply_loose(&z2),
                None => self.z.double_loose(),
            };
            let f = d.subtract_loose(&c);
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
            let double_e = x.add_loose(&y).square_loose().subtract_loose_sum(&xx, &yy);
            let double_h = WideFe::negate_loose_sum(&xx, &yy);
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
        fn double_from_affine(&self) -> Self {
            debug_assert!(
                self.z.equals_lanes(&WideFe::one()).iter().all(|&eq| eq),
                "double_from_affine requires z == 1 in every lane"
            );
            self.double_impl::<true, true>()
        }
        /// Initialization-only affine doubling, isolated so using SIMD during
        /// setup does not outline this operation in the verification hot path.
        #[inline(never)]
        fn cold_double_from_affine(&self) -> Self {
            debug_assert!(
                self.z.equals_lanes(&WideFe::one()).iter().all(|&eq| eq),
                "cold_double_from_affine requires z == 1 in every lane"
            );
            let a = self.x.square_loose();
            let b = self.y.square_loose();
            let e = self
                .x
                .add_loose(&self.y)
                .square_loose()
                .subtract_loose_sum(&a, &b);
            let g = b.subtract_loose(&a);
            let f = b.subtract_loose_sum_with_doubled_rhs(&a, &WideFe::one());
            let h = WideFe::negate_loose_sum(&a, &b);

            Self {
                x: e.multiply(&f),
                y: g.multiply(&h),
                t: e.multiply(&h),
                z: f.multiply(&g),
            }
        }
        fn double_without_t(&self) -> Self {
            self.double_impl::<false, false>()
        }

        /// In place so `acc = acc.double_four_times()`'s 1280-byte return
        /// copy never happens; the last double writes straight into `self`.
        #[inline(never)]
        fn double_four_times_assign(&mut self) {
            let tripled = self
                .double_without_t()
                .double_without_t()
                .double_without_t();
            tripled.double_into(self);
        }
        /// Inlined body stores its result directly through `out`, which a
        /// returned `Self` assigned across a call boundary does not.
        #[inline(always)]
        fn double_into(&self, out: &mut Self) {
            *out = self.double_impl::<true, false>();
        }
        // Always inline: callers embed it exactly once each, and the inlined
        // body lets an `_into` destination receive direct stores.
        #[inline(always)]
        fn double_impl<const COMPUTE_T: bool, const AFFINE_Z: bool>(&self) -> Self {
            // Loose squares feed additive ops; use loose-input subtract/negate for
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
                .subtract_loose_sum(&a, &b);
            let g = b.subtract_loose(&a);
            // `f = b - a - 2*z^2`; the factor of two rides along in the subtract.
            let f = b.subtract_loose_sum_with_doubled_rhs(&a, &z2);
            let h = WideFe::negate_loose_sum(&a, &b);
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
    /// Expand a per-lane bitmask into bools; shared with the scalar driver.
    pub(crate) fn mask_to_lanes(mask: u8) -> [bool; LANES] {
        core::array::from_fn(|lane| (mask & (1 << lane)) != 0)
    }
    #[cfg(test)]
    mod tests {
        use super::*;
        use serde_json::Value;

        const VECTOR_JSON: &str = include_str!("../tests/vectors/avx512ifma.json");

        fn vectors() -> Value {
            serde_json::from_str(VECTOR_JSON).expect("valid AVX-512 IFMA vectors")
        }

        fn vector_cases<'a>(vectors: &'a Value, name: &str) -> &'a [Value] {
            vectors[name]
                .as_array()
                .unwrap_or_else(|| panic!("{name} must be an array"))
        }

        fn hex_32(value: &Value) -> [u8; POINT_ENCODING_LEN] {
            let mut out = [0u8; POINT_ENCODING_LEN];
            hex::decode_to_slice(
                value.as_str().expect("hex vector must be a string"),
                &mut out,
            )
            .expect("valid 32-byte vector");
            out
        }

        fn limbs(value: &Value) -> [u64; LIMB_COUNT] {
            let values = value.as_array().expect("limbs must be an array");
            assert_eq!(values.len(), LIMB_COUNT);
            core::array::from_fn(|i| values[i].as_u64().expect("limb must be a u64"))
        }

        fn wide_from_rows(rows: [[u64; LANES]; LIMB_COUNT]) -> WideFe {
            WideFe {
                limbs: core::array::from_fn(|i| loadu(rows[i])),
            }
        }

        fn wide_rows(value: WideFe) -> [[u64; LANES]; LIMB_COUNT] {
            let mut rows = [[0u64; LANES]; LIMB_COUNT];
            for (limb, row) in rows.iter_mut().enumerate() {
                storeu(value.limbs[limb], row);
            }
            rows
        }

        fn wide_from_case_inputs(cases: &[Value], name: &str, offset: usize) -> WideFe {
            assert_eq!(cases.len(), LANES);
            let by_lane: [[u64; LIMB_COUNT]; LANES] =
                core::array::from_fn(|lane| limbs(&cases[(lane + offset) % LANES][name]));
            wide_from_rows(core::array::from_fn(|limb| {
                core::array::from_fn(|lane| by_lane[lane][limb])
            }))
        }

        fn assert_wide_bytes(actual: WideFe, cases: &[Value], expected_name: &str, offset: usize) {
            let actual = actual.to_bytes_lanes();
            for lane in 0..LANES {
                assert_eq!(
                    actual[lane],
                    hex_32(&cases[(lane + offset) % LANES][expected_name]),
                    "{expected_name} lane {lane}"
                );
            }
        }

        fn cached_encoding(point: &CachedPoint) -> [u8; POINT_ENCODING_LEN] {
            let (y_plus_x, y_minus_x, z2, _) = point.coords();
            let y_plus_x = WideFe::from_field_refs(&[y_plus_x; LANES]);
            let y_minus_x = WideFe::from_field_refs(&[y_minus_x; LANES]);
            let point = WidePoint {
                x: y_plus_x.subtract(&y_minus_x),
                y: y_plus_x.add_loose(&y_minus_x),
                z: WideFe::from_field_refs(&[z2; LANES]),
                t: WideFe::zero(),
            };
            point.compress()[0]
        }

        fn affine_cached_encoding(point: &AffineCachedPoint) -> [u8; POINT_ENCODING_LEN] {
            let (y_plus_x, y_minus_x, _) = point.coords();
            let y_plus_x = WideFe::from_field_refs(&[y_plus_x; LANES]);
            let y_minus_x = WideFe::from_field_refs(&[y_minus_x; LANES]);
            let point = WidePoint {
                x: y_plus_x.subtract(&y_minus_x),
                y: y_plus_x.add_loose(&y_minus_x),
                z: WideFe::one().double(),
                t: WideFe::zero(),
            };
            point.compress()[0]
        }

        fn strict_square_n(x: &WideFe, n: usize) -> WideFe {
            let mut out = *x;
            for _ in 0..n {
                out = out.square();
            }
            out
        }

        #[test]
        fn canonical_matches_vectors() {
            let vectors = vectors();
            let cases = vector_cases(&vectors, "canonical");
            assert_eq!(cases.len(), LANES);

            let by_lane: [[u64; LIMB_COUNT]; LANES] =
                core::array::from_fn(|lane| limbs(&cases[lane]["input_limbs"]));
            let wide = wide_from_rows(core::array::from_fn(|limb| {
                core::array::from_fn(|lane| by_lane[lane][limb])
            }));
            let actual = wide_rows(wide.canonical());
            let is_zero = wide.is_zero_lanes();
            let is_odd = wide.is_odd_lanes();

            for lane in 0..LANES {
                let expected = limbs(&cases[lane]["expected_limbs"]);
                let actual_lane = core::array::from_fn(|limb| actual[limb][lane]);
                assert_eq!(actual_lane, expected, "canonical lane {lane}");
                assert_eq!(
                    is_zero[lane],
                    expected == [0; LIMB_COUNT],
                    "zero lane {lane}"
                );
                assert_eq!(is_odd[lane], expected[0] & 1 != 0, "odd lane {lane}");
            }
        }

        #[test]
        fn wide_field_operations_match_vectors() {
            let vectors = vectors();
            let cases = vector_cases(&vectors, "field");
            let a = wide_from_case_inputs(cases, "a_limbs", 0);
            let b = wide_from_case_inputs(cases, "b_limbs", 0);
            let c = wide_from_case_inputs(cases, "c_limbs", 0);

            assert_wide_bytes(a.add(&b), cases, "add", 0);
            assert_wide_bytes(a.add_loose(&b), cases, "add", 0);
            assert_wide_bytes(a.subtract(&b), cases, "subtract", 0);
            assert_wide_bytes(a.multiply(&b), cases, "multiply", 0);
            assert_wide_bytes(a.multiply_loose(&b), cases, "multiply", 0);
            assert_wide_bytes(a.square(), cases, "square", 0);
            assert_wide_bytes(a.square_loose(), cases, "square", 0);

            let ab = a.multiply_loose(&b);
            let bc = b.multiply_loose(&c);
            let cc = c.square_loose();
            assert_wide_bytes(ab.subtract_loose(&bc), cases, "subtract_loose", 0);
            assert_wide_bytes(ab.subtract_loose_sum(&bc, &cc), cases, "subtract_sum", 0);
            assert_wide_bytes(
                ab.subtract_loose_sum_with_doubled_rhs(&bc, &cc),
                cases,
                "subtract_sum_doubled",
                0,
            );
            assert_wide_bytes(WideFe::negate_loose_sum(&bc, &cc), cases, "negate_sum", 0);
        }

        #[test]
        fn loose_limb0_bound_matches_vectors() {
            let vectors = vectors();
            let cases = vector_cases(&vectors, "loose_bound");
            let wide = wide_from_case_inputs(cases, "input_limbs", 0);

            assert_wide_bytes(wide.subtract_loose(&wide), cases, "zero", 0);
            assert_wide_bytes(wide.subtract_loose_sum(&wide, &wide), cases, "negate", 0);
            assert_wide_bytes(
                wide.subtract_loose_sum_with_doubled_rhs(&wide, &wide),
                cases,
                "double_negate",
                0,
            );
            assert_wide_bytes(
                WideFe::negate_loose_sum(&wide, &wide),
                cases,
                "double_negate",
                0,
            );
            assert_wide_bytes(wide.square(), cases, "square", 0);
            assert_wide_bytes(wide.square_loose(), cases, "square", 0);
        }

        #[test]
        fn square_repeat_variants_match_strict_simd_result() {
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
                        "square_repeat_x2::<{}> diverged for a",
                        $n
                    );
                    assert!(
                        xb.equals_lanes(&strict_square_n(&b, $n)).iter().all(|&v| v),
                        "square_repeat_x2::<{}> diverged for b",
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
        fn pow_variants_match_vectors() {
            let vectors = vectors();
            let cases = vector_cases(&vectors, "field");
            let a = wide_from_case_inputs(cases, "a_limbs", 0);
            let b = wide_from_case_inputs(cases, "a_limbs", 3);

            assert_wide_bytes(a.pow_p_minus_5_over_8(), cases, "pow_a", 0);
            assert_wide_bytes(b.pow_p_minus_5_over_8(), cases, "pow_a", 3);

            let (paired_a, paired_b) = WideFe::pow_p_minus_5_over_8_x2(&a, &b);
            assert_wide_bytes(paired_a, cases, "pow_a", 0);
            assert_wide_bytes(paired_b, cases, "pow_a", 3);
        }

        #[test]
        fn wide_decompression_matches_vectors() {
            let vectors = vectors();
            let cases = vector_cases(&vectors, "decompression");

            for chunk in cases.chunks(LANES) {
                let encodings = core::array::from_fn(|lane| {
                    hex_32(&chunk.get(lane).unwrap_or(&chunk[0])["encoding"])
                });
                let (point, mask) = decompress_points_wide(&encodings);
                let normalized = point.compress();

                for lane in 0..chunk.len() {
                    let expected_valid = chunk[lane]["valid"].as_bool().expect("valid is a bool");
                    assert_eq!(
                        mask & (1 << lane) != 0,
                        expected_valid,
                        "{} validity",
                        chunk[lane]["name"].as_str().unwrap()
                    );
                    if expected_valid {
                        assert_eq!(
                            normalized[lane],
                            hex_32(&chunk[lane]["normalized"]),
                            "{} normalization",
                            chunk[lane]["name"].as_str().unwrap()
                        );
                    }
                }
            }
        }

        #[test]
        fn paired_compression_matches_independent_inversions() {
            let vectors = vectors();
            let cases: Vec<&Value> = vector_cases(&vectors, "decompression")
                .iter()
                .filter(|case| case["valid"].as_bool() == Some(true))
                .take(LANES)
                .collect();
            assert_eq!(
                cases.len(),
                LANES,
                "vectors include one valid point per lane"
            );
            let encodings = core::array::from_fn(|lane| hex_32(&cases[lane]["encoding"]));
            let (point, mask) = decompress_points_wide(&encodings);
            assert_eq!(mask, u8::MAX);

            // Move away from affine Z=1 so this exercises both reciprocals in
            // Montgomery's trick, not merely the encoding shared by the inputs.
            let first = point.double();
            let second = first.double();
            let expected = (first.compress(), second.compress());
            assert_eq!(WidePoint::compress_pair(&first, &second), expected);
        }

        #[test]
        fn cached_tables_match_basepoint_vectors() {
            let vectors = vectors();
            let cases = vector_cases(&vectors, "basepoint_multiples");
            let public_table =
                decode_public_key_table(&BASEPOINT_COMPRESSED).expect("basepoint decodes");
            let base_table = BasepointTable::new();

            for case in cases {
                let scalar = case["scalar"].as_i64().expect("scalar is an integer") as i16;
                let expected = hex_32(&case["encoding"]);
                assert_eq!(
                    affine_cached_encoding(select_signed_affine_cached_ref(
                        base_table.entries(),
                        scalar,
                    )),
                    expected,
                    "fixed-base table digit {scalar}"
                );
                if (-8..=8).contains(&scalar) {
                    assert_eq!(
                        cached_encoding(public_table.select_signed_cached_ref(scalar as i8)),
                        expected,
                        "public-key table digit {scalar}"
                    );
                }
            }
        }

        #[test]
        fn wide_torsion_operations_match_vectors() {
            let vectors = vectors();
            let cases = vector_cases(&vectors, "torsion_multiples");
            let encoding = |multiple: u64| {
                hex_32(
                    &cases
                        .iter()
                        .find(|case| case["multiple"].as_u64() == Some(multiple))
                        .expect("torsion multiple is present")["encoding"],
                )
            };

            let (point, mask) = decompress_points_wide(&[encoding(1); LANES]);
            assert_eq!(mask, u8::MAX);
            assert_eq!(point.compress()[0], encoding(1));

            let doubled = point.double();
            assert_eq!(doubled.compress()[0], encoding(2));
            let quadrupled = doubled.double();
            assert_eq!(quadrupled.compress()[0], encoding(4));
            let multiplied_by_eight = quadrupled.double();
            assert_eq!(multiplied_by_eight.compress()[0], encoding(8));

            let (identity, identity_mask) = decompress_points_wide(&[encoding(8); LANES]);
            assert_eq!(identity_mask, u8::MAX);
            let subtract_chain = identity.subtract(&point).double().double().double();
            assert_eq!(subtract_chain.compress()[0], encoding(8));
        }

        #[test]
        fn wide_multiscalar_identity_key_is_identity() {
            let table = PointTable::identity();
            let base_table = BasepointTable::new();
            let s_digits = [[0i8; 64]; LANES];
            let mut one_bytes = [0u8; 32];
            one_bytes[0] = 1;
            let k = crate::scalar::Scalar::from_canonical_bytes(one_bytes);
            let k_digits = [k.to_radix16(); LANES];
            let prepared = PreparedChunk {
                public_key_tables: [&table; LANES],
                s_digits: &s_digits,
                k_digits: &k_digits,
            };
            let combined = mul_s_base_minus_k_public::<true>(base_table.entries(), &prepared);
            let mut identity = [0u8; POINT_ENCODING_LEN];
            identity[0] = 1;
            assert_eq!(combined.compress()[0], identity);
        }
    }
}
