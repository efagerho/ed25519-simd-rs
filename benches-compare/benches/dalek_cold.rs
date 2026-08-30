use criterion::{Criterion, criterion_group, criterion_main};
use ed25519_simd::DalekPolicy;

pub mod support;

macro_rules! dalek_bench {
    ($name:ident, $target:ident) => {
        fn $name(c: &mut Criterion) {
            support::$target::<DalekPolicy>(c);
        }
    };
}

dalek_bench!(distinct_keys_len1, cold_distinct_keys_len1);
dalek_bench!(distinct_keys_len1024, cold_distinct_keys_len1024);
dalek_bench!(distinct_keys_mixed_len, cold_distinct_keys_mixed_len);
dalek_bench!(ragged_batches, cold_ragged_batches);
dalek_bench!(malformed_25, cold_malformed_25);
dalek_bench!(malformed_50, cold_malformed_50);
dalek_bench!(well_formed_invalid_25, cold_well_formed_invalid_25);
dalek_bench!(well_formed_invalid_50, cold_well_formed_invalid_50);
dalek_bench!(hot_keys_4, cold_hot_keys_4);

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
