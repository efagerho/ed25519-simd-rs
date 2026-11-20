use super::LANES;
use super::point::WidePoint;
use crate::edwards::{
    AffineCachedPoint, BasepointTableEntries, CachedPoint, select_signed_affine_cached_ref,
};
use crate::wide::PreparedChunk;

pub(super) struct SelectedRound<'a> {
    odd: [&'a CachedPoint; LANES],
    base: [&'a AffineCachedPoint; LANES],
    even: [&'a CachedPoint; LANES],
}

pub(super) fn round_selector<'a>(
    base: &'a BasepointTableEntries,
    prepared: &'a PreparedChunk<'_>,
) -> impl Fn(usize) -> SelectedRound<'a> + 'a {
    move |pair| {
        let even = 2 * pair;
        let odd = even + 1;
        let public = |i: usize| {
            core::array::from_fn(|lane| {
                prepared.public_key_tables[lane]
                    .select_signed_cached_ref(-prepared.k_digits[lane][i])
            })
        };
        SelectedRound {
            odd: public(odd),
            base: core::array::from_fn(|lane| {
                let s = &prepared.s_digits[lane];
                select_signed_affine_cached_ref(base, i16::from(s[even]) + 16 * i16::from(s[odd]))
            }),
            even: public(even),
        }
    }
}

impl SelectedRound<'_> {
    pub(super) fn start(&self) -> WidePoint {
        let mut acc = WidePoint::from_cached_refs_without_t(&self.odd);
        acc.double_four_times_assign();
        acc.add_affine_cached_refs_assign(&self.base);
        acc.add_cached_refs_assign(&self.even, false);
        acc
    }

    pub(super) fn step(&self, acc: &mut WidePoint, compute_t: bool) {
        acc.double_four_times_assign();
        acc.add_cached_refs_assign(&self.odd, false);
        acc.double_four_times_assign();
        acc.add_affine_cached_refs_assign(&self.base);
        acc.add_cached_refs_assign(&self.even, compute_t);
    }
}

// Only ZIP-215's final torsion subtraction needs T.
pub(super) fn mul_s_base_minus_k_public<const NEED_T: bool>(
    base_table: &BasepointTableEntries,
    prepared: &PreparedChunk<'_>,
) -> WidePoint {
    let select = round_selector(base_table, prepared);
    let mut acc = select(31).start();
    for pair in (0..31).rev() {
        select(pair).step(&mut acc, NEED_T && pair == 0);
    }
    acc
}
