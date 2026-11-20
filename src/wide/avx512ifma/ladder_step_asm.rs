use super::LANES;
use super::field::WideFe;
use super::point::WidePoint;
use crate::edwards::{AffineCachedPoint, BasepointTableEntries, CachedPoint, PointTable};
use crate::scalar::Radix16;
use crate::wide::PreparedChunk;
use core::mem::MaybeUninit;

core::arch::global_asm!(include_str!("stage_round.S"), options(raw));
core::arch::global_asm!(include_str!("ladder_step.S"), options(raw));

/// The operand layout consumed by the linked ladder_step.S.
#[repr(C)]
pub(super) struct StagedLadderStep {
    odd: [WideFe; 4],
    base: [WideFe; 3],
    even: [WideFe; 4],
}

const _: () = {
    use core::mem::{align_of, offset_of, size_of};
    assert!(size_of::<Radix16>() == 64 && LANES == 8);
    assert!(align_of::<StagedLadderStep>() == 64);
    assert!(size_of::<StagedLadderStep>() == 3520);
    assert!(offset_of!(StagedLadderStep, odd) == 0);
    assert!(offset_of!(StagedLadderStep, base) == 1280);
    assert!(offset_of!(StagedLadderStep, even) == 2240);
};

unsafe extern "C" {
    fn ed25519_simd_stage_round(
        out: *mut u8,
        keys: *const *const CachedPoint,
        base: *const AffineCachedPoint,
        s: *const Radix16,
        k: *const Radix16,
        pair: usize,
    );
    fn ed25519_simd_ladder_step_ifma(point: *mut u8, operands: *const u8, compute_t: u64);
}

/// Borrow the tables for the entire ladder and resolve their entry-array
/// addresses once. Each invocation materializes only the requested pair.
pub(super) fn round_selector<'a>(
    base: &'a BasepointTableEntries,
    prepared: &'a PreparedChunk<'_>,
) -> impl Fn(usize) -> StagedLadderStep + 'a {
    let keys = prepared.public_key_tables.map(PointTable::entries_ptr);
    move |pair| {
        assert!(pair < 32);
        let mut out = MaybeUninit::<StagedLadderStep>::uninit();
        // SAFETY: the sources remain borrowed, and pair selects two bytes
        // within each digit row. The assembly bounds both table indices by
        // extracting nibbles. Every load fits in its initialized table entry,
        // and every limb of the exclusive, aligned output is written.
        unsafe {
            ed25519_simd_stage_round(
                out.as_mut_ptr().cast(),
                keys.as_ptr(),
                base.as_ptr(),
                prepared.s_digits.as_ptr(),
                prepared.k_digits.as_ptr(),
                pair,
            );
            out.assume_init()
        }
    }
}

impl StagedLadderStep {
    /// Pair 31 seeds XYZ from the odd cached point. The first doubling
    /// ignores T. The base addition supplies T for the even addition.
    pub(super) fn start(&self) -> WidePoint {
        let [ymx, ypx, _, z2] = &self.odd;
        let mut acc = WidePoint::from_cached_fields_without_t(ymx, ypx, *z2);
        acc.double_four_times_assign();
        acc.add_staged_cached_assign(&self.base, true);
        acc.add_staged_cached_assign(&self.even, false);
        acc
    }

    #[inline]
    pub(super) fn step(&self, point: &mut WidePoint, compute_t: bool) {
        #[cfg(debug_assertions)]
        for field in self.odd.iter().chain(&self.base).chain(&self.even) {
            debug_assert!(super::field::limbs_are_ifma_operands(&field.limbs));
        }
        // SAFETY: the accumulator and staged operands are disjoint and
        // aligned. Tables supply 52-bit cached limbs. Each ladder result
        // satisfies the next double4 input bounds, including when T is zero.
        unsafe {
            ed25519_simd_ladder_step_ifma(
                core::ptr::from_mut(point).cast(),
                core::ptr::from_ref(self).cast(),
                u64::from(compute_t),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::edwards::{BASEPOINT_TABLE_SIZE, select_signed_affine_cached_ref};
    use crate::field::Fe51;

    // Differentiate the table, signed entry, coordinate and limb in every
    // word so that a lane swap or an incorrect tile boundary is observable.
    fn field(table: usize, entry: usize, coord: usize) -> Fe51 {
        Fe51::from_limbs_unchecked(core::array::from_fn(|limb| {
            (1 << 51) + (table * 100000 + entry * 20 + coord * 5 + limb) as u64
        }))
    }

    #[test]
    fn stage_round_matches_signed_lookup_for_every_digit_pair_and_lane() {
        let tables: [_; LANES] = core::array::from_fn(|lane| {
            let mut table = PointTable::identity();
            let entry = |i| {
                CachedPoint::from_fields(
                    field(lane, i, 0),
                    field(lane, i, 1),
                    field(lane, i, 2),
                    field(lane, i, 3),
                )
            };
            for m in 1..=8 {
                table.set_multiple(m, entry(8 + m), entry(8 - m));
            }
            table
        });
        let base: Box<BasepointTableEntries> = (0..=2 * BASEPOINT_TABLE_SIZE)
            .map(|i| AffineCachedPoint::from_fields(field(8, i, 0), field(8, i, 1), field(8, i, 2)))
            .collect::<Vec<_>>()
            .into_boxed_slice()
            .try_into()
            .unwrap();

        #[repr(C, align(64))]
        struct Guarded {
            before: [u64; 8],
            words: [[u64; LANES]; 55],
            after: [u64; 8],
        }
        for batch in 0..8 {
            let keys: [_; LANES] = core::array::from_fn(|lane| {
                if batch == 0 {
                    &tables[0]
                } else {
                    &tables[(lane + batch) % LANES]
                }
            });
            let entry_ptrs = keys.map(PointTable::entries_ptr);
            let s: [Radix16; LANES] = core::array::from_fn(|lane| {
                core::array::from_fn(|i| {
                    let index = 8 * (i / 2) + (lane + batch) % 8;
                    (if i % 2 == 0 { index % 16 } else { index / 16 }) as i8 - 8
                })
            });
            let k: [Radix16; LANES] = core::array::from_fn(|lane| {
                core::array::from_fn(|i| ((i + 5 * lane + batch) % 16) as i8 - 8)
            });
            for pair in 0..32 {
                let mut out = Guarded {
                    before: [0xa5; 8],
                    words: [[u64::MAX; LANES]; 55],
                    after: [0x5a; 8],
                };
                // SAFETY: same extents and alignment as StagedLadderStep, with
                // an initialized sentinel in every destination word and guard.
                unsafe {
                    ed25519_simd_stage_round(
                        out.words.as_mut_ptr().cast(),
                        entry_ptrs.as_ptr(),
                        base.as_ptr(),
                        s.as_ptr(),
                        k.as_ptr(),
                        pair,
                    );
                }
                assert_eq!(out.before, [0xa5; 8]);
                assert_eq!(out.after, [0x5a; 8]);
                for lane in 0..LANES {
                    let digit = 2 * pair;
                    let odd = keys[lane]
                        .select_signed_cached_ref(-k[lane][digit + 1])
                        .coords();
                    let even = keys[lane]
                        .select_signed_cached_ref(-k[lane][digit])
                        .coords();
                    let folded = i16::from(s[lane][digit]) + 16 * i16::from(s[lane][digit + 1]);
                    let b = select_signed_affine_cached_ref(&base, folded).coords();
                    let fields = [
                        odd.1, odd.0, odd.3, odd.2, b.1, b.0, b.2, even.1, even.0, even.3, even.2,
                    ];
                    for (f, field) in fields.iter().enumerate() {
                        for (i, limb) in field.loose_limbs().into_iter().enumerate() {
                            assert_eq!(
                                out.words[5 * f + i][lane],
                                limb,
                                "pair={pair} lane={lane} field={f} limb={i}"
                            );
                        }
                    }
                }
            }
        }
    }
}
