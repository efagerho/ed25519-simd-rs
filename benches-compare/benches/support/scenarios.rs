use std::hint::black_box;

use criterion::{BenchmarkGroup, BenchmarkId, Criterion, Throughput, measurement::WallTime};
use ed25519_simd::{
    HotKeyCache, NullKeyCache, VerificationPolicy, Verifier, VerifyInput, VerifyPolicy,
};

use super::backends::*;
use super::cases::*;

fn policy_name<P: VerificationPolicy>() -> &'static str {
    match P::POLICY {
        VerifyPolicy::Zip215 => "zip215",
        VerifyPolicy::Dalek => "dalek",
    }
}

fn bench_ours_nocache<P: VerificationPolicy>(
    group: &mut BenchmarkGroup<'_, WallTime>,
    name: &str,
    n: usize,
    inputs: &[VerifyInput<'_>],
) {
    group.bench_with_input(BenchmarkId::new(name, n), &n, |b, _| {
        let mut verifier = Verifier::<P, _>::with_cache(NullKeyCache::new());
        let mut out = vec![false; inputs.len()];
        b.iter(|| {
            verifier.verify_batch(black_box(inputs), &mut out);
            black_box(out.iter().all(|accepted| *accepted))
        })
    });
}

/// Reuse one verifier/cache so iterations measure steady-state hot-key hits.
fn bench_ours_hot_key_cache<P: VerificationPolicy>(
    group: &mut BenchmarkGroup<'_, WallTime>,
    name: &str,
    n: usize,
    hot_key_count: usize,
    inputs: &[VerifyInput<'_>],
) {
    group.bench_with_input(BenchmarkId::new(name, n), &n, |b, _| {
        let mut verifier = Verifier::<P, _>::with_cache(HotKeyCache::with_capacity(hot_key_count));
        let mut out = vec![false; inputs.len()];
        b.iter(|| {
            verifier.verify_batch(black_box(inputs), &mut out);
            black_box(out.iter().all(|accepted| *accepted))
        })
    });
}

/// Measure the null-cache configuration on `hot_key_count` repeating keys.
fn bench_cold_hot_keys_scenario<P: VerificationPolicy>(
    c: &mut Criterion,
    group_name: &str,
    hot_key_count: usize,
) {
    let mut group = c.benchmark_group(group_name);
    for n in SIZES {
        let cases = generate_hot_key_cases(n, hot_key_count, MsgLen::Fixed(1));
        let inputs = inputs_of(&cases);
        group.throughput(Throughput::Elements(n as u64));

        bench_ours_nocache::<P>(
            &mut group,
            &format!("ed25519_simd_nullcache/{}", policy_name::<P>()),
            n,
            &inputs,
        );
    }
    group.finish();
}

/// Measure steady-state hot-cache hits on `hot_key_count` repeating keys.
fn bench_hot_keys_scenario<P: VerificationPolicy>(
    c: &mut Criterion,
    group_name: &str,
    hot_key_count: usize,
) {
    let mut group = c.benchmark_group(group_name);
    for n in SIZES {
        let cases = generate_hot_key_cases(n, hot_key_count, MsgLen::Fixed(1));
        let inputs = inputs_of(&cases);
        group.throughput(Throughput::Elements(n as u64));

        bench_ours_hot_key_cache::<P>(
            &mut group,
            &format!("ed25519_simd_hotcache/{}", policy_name::<P>()),
            n,
            hot_key_count,
            &inputs,
        );
    }
    group.finish();
}

fn bench_cold_scenario<P: VerificationPolicy, const COMPARISONS: bool>(
    c: &mut Criterion,
    group_name: &str,
    msg_len: MsgLen,
) {
    let mut group = c.benchmark_group(group_name);
    for n in SIZES {
        let cases = generate_distinct_key_cases(n, msg_len);
        let inputs = inputs_of(&cases);
        group.throughput(Throughput::Elements(n as u64));

        bench_ours_nocache::<P>(
            &mut group,
            &format!("ed25519_simd_nocache/{}", policy_name::<P>()),
            n,
            &inputs,
        );
        if COMPARISONS && P::POLICY == VerifyPolicy::Dalek {
            group.bench_with_input(
                BenchmarkId::new("solana_ed25519/dalek_loop", n),
                &n,
                |b, _| b.iter(|| solana_ed25519_dalek_loop(black_box(&inputs))),
            );
            group.bench_with_input(BenchmarkId::new("ed25519_dalek/batch", n), &n, |b, _| {
                b.iter(|| dalek_batch(black_box(&inputs)))
            });
            group.bench_with_input(BenchmarkId::new("ed25519_dalek/loop", n), &n, |b, _| {
                b.iter(|| dalek_loop(black_box(&inputs)))
            });
            group.bench_with_input(BenchmarkId::new("aws_lc_rs/loop", n), &n, |b, _| {
                b.iter(|| aws_lc_loop(black_box(&inputs)))
            });
            group.bench_with_input(BenchmarkId::new("ring/loop", n), &n, |b, _| {
                b.iter(|| ring_loop(black_box(&inputs)))
            });
            init_sodiumoxide();
            group.bench_with_input(BenchmarkId::new("sodiumoxide/loop", n), &n, |b, _| {
                b.iter(|| sodium_loop(black_box(&inputs)))
            });
            group.bench_with_input(BenchmarkId::new("openssl/loop", n), &n, |b, _| {
                b.iter(|| openssl_loop(black_box(&inputs)))
            });
        } else if COMPARISONS {
            group.bench_with_input(
                BenchmarkId::new("solana_ed25519/zip215_batch", n),
                &n,
                |b, _| b.iter(|| solana_ed25519_batch_zip215(black_box(&inputs))),
            );
        }
    }
    group.finish();
}

fn bench_cold_ragged_batches<P: VerificationPolicy>(c: &mut Criterion) {
    let mut group = c.benchmark_group("ragged_batches/msg_len_1");
    for n in RAGGED_SIZES {
        let cases = generate_distinct_key_cases(n, MsgLen::Fixed(1));
        let inputs = inputs_of(&cases);
        group.throughput(Throughput::Elements(n as u64));

        bench_ours_nocache::<P>(
            &mut group,
            &format!("ed25519_simd_nullcache/{}", policy_name::<P>()),
            n,
            &inputs,
        );
    }
    group.finish();
}

fn bench_hot_ragged_batches<P: VerificationPolicy>(c: &mut Criterion) {
    let mut group = c.benchmark_group("ragged_batches/msg_len_1");
    for n in RAGGED_SIZES {
        let cases = generate_distinct_key_cases(n, MsgLen::Fixed(1));
        let inputs = inputs_of(&cases);
        group.throughput(Throughput::Elements(n as u64));

        bench_ours_hot_key_cache::<P>(
            &mut group,
            &format!("ed25519_simd_hotcache/{}", policy_name::<P>()),
            n,
            n,
            &inputs,
        );
    }
    group.finish();
}

fn bench_cold_invalid_scenario<P: VerificationPolicy, const COMPARISONS: bool>(
    c: &mut Criterion,
    group_name: &str,
    invalid_pct: u64,
    kind: InvalidKind,
) {
    let mut group = c.benchmark_group(group_name);
    for n in SIZES {
        let mut cases = generate_distinct_key_cases(n, MsgLen::Fixed(1));
        invalidate_fraction(&mut cases, invalid_pct, kind);
        let inputs = inputs_of(&cases);
        group.throughput(Throughput::Elements(n as u64));

        bench_ours_nocache::<P>(
            &mut group,
            &format!("ed25519_simd_nocache/{}", policy_name::<P>()),
            n,
            &inputs,
        );
        if COMPARISONS && P::POLICY == VerifyPolicy::Dalek {
            group.bench_with_input(BenchmarkId::new("ed25519_dalek/batch", n), &n, |b, _| {
                b.iter(|| dalek_batch(black_box(&inputs)))
            });
            group.bench_with_input(BenchmarkId::new("ed25519_dalek/loop", n), &n, |b, _| {
                b.iter(|| dalek_loop(black_box(&inputs)))
            });
            group.bench_with_input(
                BenchmarkId::new("solana_ed25519/dalek_loop", n),
                &n,
                |b, _| b.iter(|| solana_ed25519_dalek_loop(black_box(&inputs))),
            );
        } else if COMPARISONS {
            group.bench_with_input(
                BenchmarkId::new("solana_ed25519/zip215_batch", n),
                &n,
                |b, _| b.iter(|| solana_ed25519_batch_zip215(black_box(&inputs))),
            );
        }
    }
    group.finish();
}

pub fn cold_distinct_keys_len1<P: VerificationPolicy, const COMPARISONS: bool>(c: &mut Criterion) {
    bench_cold_scenario::<P, COMPARISONS>(c, "distinct_keys/msg_len_1", MsgLen::Fixed(1));
}

pub fn cold_malformed_25<P: VerificationPolicy, const COMPARISONS: bool>(c: &mut Criterion) {
    bench_cold_invalid_scenario::<P, COMPARISONS>(
        c,
        "malformed_sigs/invalid_25pct",
        25,
        InvalidKind::MalformedSignature,
    );
}

pub fn cold_malformed_50<P: VerificationPolicy, const COMPARISONS: bool>(c: &mut Criterion) {
    bench_cold_invalid_scenario::<P, COMPARISONS>(
        c,
        "malformed_sigs/invalid_50pct",
        50,
        InvalidKind::MalformedSignature,
    );
}

pub fn cold_well_formed_invalid_25<P: VerificationPolicy, const COMPARISONS: bool>(
    c: &mut Criterion,
) {
    bench_cold_invalid_scenario::<P, COMPARISONS>(
        c,
        "well_formed_invalid/wrong_message_25pct",
        25,
        InvalidKind::WellFormedWrongMessage,
    );
}

pub fn cold_well_formed_invalid_50<P: VerificationPolicy, const COMPARISONS: bool>(
    c: &mut Criterion,
) {
    bench_cold_invalid_scenario::<P, COMPARISONS>(
        c,
        "well_formed_invalid/wrong_message_50pct",
        50,
        InvalidKind::WellFormedWrongMessage,
    );
}

pub fn cold_distinct_keys_len1024<P: VerificationPolicy, const COMPARISONS: bool>(
    c: &mut Criterion,
) {
    bench_cold_scenario::<P, COMPARISONS>(c, "distinct_keys/msg_len_1024", MsgLen::Fixed(1024));
}

pub fn cold_distinct_keys_mixed_len<P: VerificationPolicy, const COMPARISONS: bool>(
    c: &mut Criterion,
) {
    bench_cold_scenario::<P, COMPARISONS>(c, "distinct_keys/msg_len_mixed", MsgLen::Mixed);
}

pub fn cold_ragged_batches<P: VerificationPolicy>(c: &mut Criterion) {
    bench_cold_ragged_batches::<P>(c);
}

pub fn cold_hot_keys_4<P: VerificationPolicy>(c: &mut Criterion) {
    bench_cold_hot_keys_scenario::<P>(c, "hot_keys/distinct_4", 4);
}

pub fn hot_ragged_batches<P: VerificationPolicy>(c: &mut Criterion) {
    bench_hot_ragged_batches::<P>(c);
}

pub fn hot_keys_4<P: VerificationPolicy>(c: &mut Criterion) {
    bench_hot_keys_scenario::<P>(c, "hot_keys/distinct_4", 4);
}
