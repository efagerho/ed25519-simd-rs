// Each configuration-specific benchmark binary registers only its cold or hot
// scenarios; the linker then discards the deliberately unused half.
#![allow(dead_code)]

mod backends;
mod cases;
mod scenarios;

pub(crate) use scenarios::*;

macro_rules! benchmark_main {
    (cold, $policy:ty, $comparisons:literal) => {
        fn distinct_keys_len1(c: &mut criterion::Criterion) {
            $crate::support::cold_distinct_keys_len1::<$policy, $comparisons>(c);
        }
        fn distinct_keys_len1024(c: &mut criterion::Criterion) {
            $crate::support::cold_distinct_keys_len1024::<$policy, $comparisons>(c);
        }
        fn distinct_keys_mixed_len(c: &mut criterion::Criterion) {
            $crate::support::cold_distinct_keys_mixed_len::<$policy, $comparisons>(c);
        }
        fn ragged_batches(c: &mut criterion::Criterion) {
            $crate::support::cold_ragged_batches::<$policy>(c);
        }
        fn malformed_25(c: &mut criterion::Criterion) {
            $crate::support::cold_malformed_25::<$policy, $comparisons>(c);
        }
        fn malformed_50(c: &mut criterion::Criterion) {
            $crate::support::cold_malformed_50::<$policy, $comparisons>(c);
        }
        fn well_formed_invalid_25(c: &mut criterion::Criterion) {
            $crate::support::cold_well_formed_invalid_25::<$policy, $comparisons>(c);
        }
        fn well_formed_invalid_50(c: &mut criterion::Criterion) {
            $crate::support::cold_well_formed_invalid_50::<$policy, $comparisons>(c);
        }
        fn hot_keys_4(c: &mut criterion::Criterion) {
            $crate::support::cold_hot_keys_4::<$policy>(c);
        }

        criterion::criterion_group!(
            benches,
            distinct_keys_len1,
            distinct_keys_len1024,
            distinct_keys_mixed_len,
            ragged_batches,
            malformed_25,
            malformed_50,
            well_formed_invalid_25,
            well_formed_invalid_50,
            hot_keys_4,
        );
        criterion::criterion_main!(benches);
    };
    (hot, $policy:ty) => {
        fn ragged_batches(c: &mut criterion::Criterion) {
            $crate::support::hot_ragged_batches::<$policy>(c);
        }
        fn hot_keys_4(c: &mut criterion::Criterion) {
            $crate::support::hot_keys_4::<$policy>(c);
        }

        criterion::criterion_group!(benches, ragged_batches, hot_keys_4);
        criterion::criterion_main!(benches);
    };
}
pub(crate) use benchmark_main;
