use criterion::{Criterion, criterion_group, criterion_main};
use ed25519_simd::Zip215Policy;

pub mod support;

macro_rules! zip215_bench {
    ($name:ident, $target:ident) => {
        fn $name(c: &mut Criterion) {
            support::$target::<Zip215Policy>(c);
        }
    };
}

zip215_bench!(distinct_keys_len1, simd_cold_distinct_keys_len1);
zip215_bench!(distinct_keys_len1024, simd_cold_distinct_keys_len1024);
zip215_bench!(distinct_keys_mixed_len, simd_cold_distinct_keys_mixed_len);
zip215_bench!(ragged_batches, cold_ragged_batches);
zip215_bench!(malformed_25, simd_cold_malformed_25);
zip215_bench!(malformed_50, simd_cold_malformed_50);
zip215_bench!(well_formed_invalid_25, simd_cold_well_formed_invalid_25);
zip215_bench!(well_formed_invalid_50, simd_cold_well_formed_invalid_50);
zip215_bench!(hot_keys_4, cold_hot_keys_4);

criterion_group!(
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
criterion_main!(benches);
