use criterion::{Criterion, criterion_group, criterion_main};
use ed25519_simd::DalekPolicy;

pub mod support;

fn ragged_batches(c: &mut Criterion) {
    support::hot_ragged_batches::<DalekPolicy>(c);
}

fn hot_keys_4(c: &mut Criterion) {
    support::hot_keys_4::<DalekPolicy>(c);
}

criterion_group!(benches, ragged_batches, hot_keys_4);
criterion_main!(benches);
