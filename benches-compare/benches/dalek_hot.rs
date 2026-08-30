use criterion::{Criterion, criterion_group, criterion_main};

pub mod support;

fn ragged_batches(c: &mut Criterion) {
    support::hot_ragged_batches::<true>(c);
}

fn hot_keys_4(c: &mut Criterion) {
    support::hot_keys_4::<true>(c);
}

criterion_group!(benches, ragged_batches, hot_keys_4);
criterion_main!(benches);
