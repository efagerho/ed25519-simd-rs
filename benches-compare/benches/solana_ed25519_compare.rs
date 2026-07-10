use core::convert::TryFrom;
use std::hint::black_box;
use std::sync::Once;

use criterion::{
    BenchmarkGroup, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main,
    measurement::WallTime,
};
use curve25519::ed_sigs::{Signature, SigningKey, VerificationKey, VerificationKeyBytes, batch};
use ed25519_dalek::{
    Signature as DalekSignature, Verifier as DalekVerifier, VerifyingKey as DalekVerifyingKey,
    verify_batch as dalek_verify_batch,
};
use ed25519_simd::{HotKeyCache, NullKeyCache, Verifier, VerifyInput, VerifyPolicy};
use openssl::{
    pkey::{Id as OpenSslId, PKey},
    sign::Verifier as OpenSslVerifier,
};
use sodiumoxide::crypto::sign::ed25519::{
    PublicKey as SodiumPublicKey, Signature as SodiumSignature, verify_detached as sodium_verify,
};

const SIZES: [usize; 4] = [8, 16, 32, 64];

/// One-time libsodium initialization, kept outside timed loops.
fn init_sodiumoxide() {
    static INIT: Once = Once::new();
    INIT.call_once(|| sodiumoxide::init().expect("failed to initialize libsodium"));
}

struct SplitMix(u64);
impl SplitMix {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
}

fn signing_key_from_index(index: u64) -> SigningKey {
    let mut seed = [0u8; 32];
    seed[..8].copy_from_slice(&index.to_le_bytes());
    SigningKey::from(seed)
}

struct Owned {
    pk: [u8; 32],
    sig: [u8; 64],
    msg: Vec<u8>,
}

#[derive(Clone, Copy)]
enum MsgLen {
    Fixed(usize),
    Mixed,
}

fn generate_distinct_keys(n: usize, msg_len: MsgLen) -> Vec<Owned> {
    let mut rng = SplitMix(0x5eed_1234);
    (0..n)
        .map(|i| {
            let key = signing_key_from_index(i as u64);
            let pk = <[u8; 32]>::from(VerificationKeyBytes::from(&key));
            let len = match msg_len {
                MsgLen::Fixed(l) => l,
                MsgLen::Mixed => (rng.next() % 257) as usize,
            };
            let mut msg = vec![0u8; len];
            for b in msg.iter_mut() {
                *b = (rng.next() & 0xff) as u8;
            }
            let sig = key.sign(&msg).to_bytes();
            Owned { pk, sig, msg }
        })
        .collect()
}

/// Signatures over a small, fixed set of keys, cycled to fill the batch —
/// the hot-key-repeat workload `HotKeyCache` is meant for.
fn generate_hot_keys(n: usize, hot_key_count: usize, msg_len: MsgLen) -> Vec<Owned> {
    let mut rng = SplitMix(0x5eed_1234);
    let hot_keys: Vec<SigningKey> = (0..hot_key_count)
        .map(|i| signing_key_from_index(i as u64))
        .collect();
    (0..n)
        .map(|i| {
            let key = &hot_keys[i % hot_key_count];
            let pk = <[u8; 32]>::from(VerificationKeyBytes::from(key));
            let len = match msg_len {
                MsgLen::Fixed(l) => l,
                MsgLen::Mixed => (rng.next() % 257) as usize,
            };
            let mut msg = vec![0u8; len];
            for b in msg.iter_mut() {
                *b = (rng.next() & 0xff) as u8;
            }
            let sig = key.sign(&msg).to_bytes();
            Owned { pk, sig, msg }
        })
        .collect()
}

/// Corrupt a scattered fraction of signatures while leaving keys valid.
fn corrupt_fraction(cases: &mut [Owned], invalid_pct: u64) {
    let mut st = 0x9e37_79b9_7f4a_7c15u64;
    for case in cases.iter_mut() {
        st = st.wrapping_mul(0xd134_2543_de82_ef95).wrapping_add(1);
        if (st >> 40) % 100 < invalid_pct {
            for (j, b) in case.sig.iter_mut().enumerate() {
                *b = (st >> (j % 8 * 8)) as u8;
            }
        }
    }
}

fn inputs_of(cases: &[Owned]) -> Vec<VerifyInput<'_>> {
    cases
        .iter()
        .map(|c| VerifyInput {
            public_key: c.pk,
            signature: c.sig,
            message: &c.msg,
        })
        .collect()
}

fn solana_ed25519_batch_zip215(inputs: &[VerifyInput<'_>]) -> bool {
    let mut batch = batch::Verifier::new();
    for input in inputs {
        let vk_bytes = VerificationKeyBytes::from(input.public_key);
        let sig = Signature::from(input.signature);
        batch.queue((vk_bytes, sig, input.message));
    }
    batch.verify(rand::thread_rng()).is_ok()
}

// These loops verify every element with `&`, so scattered-invalid batches do
// not short-circuit. Parsing stays inside the loop to match cold-cache backends.
fn solana_ed25519_dalek_loop(inputs: &[VerifyInput<'_>]) -> bool {
    inputs.iter().fold(true, |acc, input| {
        let vk_bytes = VerificationKeyBytes::from(input.public_key);
        let sig = Signature::from(input.signature);
        let ok = VerificationKey::try_from(vk_bytes)
            .and_then(|vk| vk.verify_dalek(&sig, input.message))
            .is_ok();
        acc & ok
    })
}

fn dalek_batch(inputs: &[VerifyInput<'_>]) -> bool {
    let messages: Vec<&[u8]> = inputs.iter().map(|input| input.message).collect();
    let signatures: Vec<DalekSignature> = inputs
        .iter()
        .map(|input| DalekSignature::from_bytes(&input.signature))
        .collect();
    let verifying_keys: Vec<DalekVerifyingKey> = inputs
        .iter()
        .map(|input| DalekVerifyingKey::from_bytes(&input.public_key).unwrap())
        .collect();
    dalek_verify_batch(&messages, &signatures, &verifying_keys).is_ok()
}

fn dalek_loop(inputs: &[VerifyInput<'_>]) -> bool {
    inputs.iter().fold(true, |acc, input| {
        let signature = DalekSignature::from_bytes(&input.signature);
        let ok = DalekVerifyingKey::from_bytes(&input.public_key)
            .map(|vk| DalekVerifier::verify(&vk, input.message, &signature).is_ok())
            .unwrap_or(false);
        acc & ok
    })
}

fn aws_lc_loop(inputs: &[VerifyInput<'_>]) -> bool {
    inputs.iter().fold(true, |acc, input| {
        let ok = aws_lc_rs::signature::ParsedPublicKey::new(
            &aws_lc_rs::signature::ED25519,
            input.public_key,
        )
        .map(|key| key.verify_sig(input.message, &input.signature).is_ok())
        .unwrap_or(false);
        acc & ok
    })
}

fn ring_loop(inputs: &[VerifyInput<'_>]) -> bool {
    inputs.iter().fold(true, |acc, input| {
        let key =
            ring::signature::UnparsedPublicKey::new(&ring::signature::ED25519, input.public_key);
        acc & key.verify(input.message, &input.signature).is_ok()
    })
}

fn sodium_loop(inputs: &[VerifyInput<'_>]) -> bool {
    inputs.iter().fold(true, |acc, input| {
        let key = SodiumPublicKey::from_slice(&input.public_key).unwrap();
        let signature = SodiumSignature::from_bytes(&input.signature).unwrap();
        acc & sodium_verify(&signature, input.message, &key)
    })
}

fn openssl_loop(inputs: &[VerifyInput<'_>]) -> bool {
    inputs.iter().fold(true, |acc, input| {
        let ok = (|| {
            let key = PKey::public_key_from_raw_bytes(&input.public_key, OpenSslId::ED25519)?;
            let mut verifier = OpenSslVerifier::new_without_digest(&key)?;
            verifier.verify_oneshot(&input.signature, input.message)
        })()
        .unwrap_or(false);
        acc & ok
    })
}

fn bench_ours_nocache(
    group: &mut BenchmarkGroup<'_, WallTime>,
    name: &str,
    policy: VerifyPolicy,
    n: usize,
    inputs: &[VerifyInput<'_>],
) {
    group.bench_with_input(BenchmarkId::new(name, n), &n, |b, _| {
        let mut verifier = Verifier::with_cache(policy, NullKeyCache::new());
        let mut out = vec![false; inputs.len()];
        b.iter(|| {
            verifier.verify_batch(black_box(inputs), &mut out);
            black_box(out.iter().all(|accepted| *accepted))
        })
    });
}

/// Reuse one verifier/cache so iterations measure steady-state hot-key hits.
fn bench_ours_hot_key_cache(
    group: &mut BenchmarkGroup<'_, WallTime>,
    name: &str,
    policy: VerifyPolicy,
    n: usize,
    hot_key_count: usize,
    inputs: &[VerifyInput<'_>],
) {
    group.bench_with_input(BenchmarkId::new(name, n), &n, |b, _| {
        let mut verifier = Verifier::with_cache(policy, HotKeyCache::with_capacity(hot_key_count));
        let mut out = vec![false; inputs.len()];
        b.iter(|| {
            verifier.verify_batch(black_box(inputs), &mut out);
            black_box(out.iter().all(|accepted| *accepted))
        })
    });
}

/// Compares `NullKeyCache` against `HotKeyCache` on a batch that repeats a
/// small set of `hot_key_count` keys, quantifying the caching win the README
/// only describes qualitatively.
fn bench_hot_keys_scenario(c: &mut Criterion, group_name: &str, hot_key_count: usize) {
    let mut group = c.benchmark_group(group_name);
    for n in SIZES {
        let cases = generate_hot_keys(n, hot_key_count, MsgLen::Fixed(1));
        let inputs = inputs_of(&cases);
        group.throughput(Throughput::Elements(n as u64));

        bench_ours_nocache(
            &mut group,
            "ed25519_simd_nullcache/zip215",
            VerifyPolicy::Zip215,
            n,
            &inputs,
        );
        bench_ours_hot_key_cache(
            &mut group,
            "ed25519_simd_hotcache/zip215",
            VerifyPolicy::Zip215,
            n,
            hot_key_count,
            &inputs,
        );
        // Phase 2h touches both policies (the split ladder computes the same
        // point); the report asserts Dalek improves consistently with Zip215.
        bench_ours_hot_key_cache(
            &mut group,
            "ed25519_simd_hotcache/dalek",
            VerifyPolicy::Dalek,
            n,
            hot_key_count,
            &inputs,
        );
    }
    group.finish();
}

fn bench_scenario(c: &mut Criterion, group_name: &str, msg_len: MsgLen) {
    let mut group = c.benchmark_group(group_name);
    for n in SIZES {
        let cases = generate_distinct_keys(n, msg_len);
        let inputs = inputs_of(&cases);
        group.throughput(Throughput::Elements(n as u64));

        bench_ours_nocache(
            &mut group,
            "ed25519_simd_nocache/zip215",
            VerifyPolicy::Zip215,
            n,
            &inputs,
        );
        group.bench_with_input(
            BenchmarkId::new("solana_ed25519/zip215_batch", n),
            &n,
            |b, _| b.iter(|| solana_ed25519_batch_zip215(black_box(&inputs))),
        );

        bench_ours_nocache(
            &mut group,
            "ed25519_simd_nocache/dalek",
            VerifyPolicy::Dalek,
            n,
            &inputs,
        );
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
    }
    group.finish();
}

/// Distinct valid keys with a scattered invalid-signature fraction.
fn bench_garbage_scenario(c: &mut Criterion, group_name: &str, invalid_pct: u64) {
    let mut group = c.benchmark_group(group_name);
    for n in SIZES {
        let mut cases = generate_distinct_keys(n, MsgLen::Fixed(1));
        corrupt_fraction(&mut cases, invalid_pct);
        let inputs = inputs_of(&cases);
        group.throughput(Throughput::Elements(n as u64));

        bench_ours_nocache(
            &mut group,
            "ed25519_simd_nocache/zip215",
            VerifyPolicy::Zip215,
            n,
            &inputs,
        );
        bench_ours_nocache(
            &mut group,
            "ed25519_simd_nocache/dalek",
            VerifyPolicy::Dalek,
            n,
            &inputs,
        );
        group.bench_with_input(
            BenchmarkId::new("solana_ed25519/zip215_batch", n),
            &n,
            |b, _| b.iter(|| solana_ed25519_batch_zip215(black_box(&inputs))),
        );
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
    }
    group.finish();
}

fn bench_distinct_keys_len1(c: &mut Criterion) {
    bench_scenario(c, "distinct_keys/msg_len_1", MsgLen::Fixed(1));
}

fn bench_garbage_25(c: &mut Criterion) {
    bench_garbage_scenario(c, "garbage_sigs/invalid_25pct", 25);
}

fn bench_garbage_50(c: &mut Criterion) {
    bench_garbage_scenario(c, "garbage_sigs/invalid_50pct", 50);
}

fn bench_distinct_keys_len1024(c: &mut Criterion) {
    bench_scenario(c, "distinct_keys/msg_len_1024", MsgLen::Fixed(1024));
}

fn bench_distinct_keys_mixed_len(c: &mut Criterion) {
    bench_scenario(c, "distinct_keys/msg_len_mixed", MsgLen::Mixed);
}

fn bench_hot_keys_4(c: &mut Criterion) {
    bench_hot_keys_scenario(c, "hot_keys/distinct_4", 4);
}

/// Cache churn: every key in the batch is distinct and the capacity is far
/// smaller, so the steady state is all-miss (keys are evicted before reuse).
/// Guard for Phase 2h lazy promotion: no A′ is ever built here, so this must
/// stay at Phase 1b levels.
fn bench_hot_keys_churn(c: &mut Criterion) {
    let mut group = c.benchmark_group("hot_keys/churn_cap4");
    for n in SIZES {
        let cases = generate_hot_keys(n, n, MsgLen::Fixed(1));
        let inputs = inputs_of(&cases);
        group.throughput(Throughput::Elements(n as u64));
        bench_ours_hot_key_cache(
            &mut group,
            "ed25519_simd_hotcache/zip215",
            VerifyPolicy::Zip215,
            n,
            4,
            &inputs,
        );
    }
    group.finish();
}

/// Large hot-key working sets: fully distinct keys (`hot_key_count == n`), all
/// resident after warmup. At 256/1024 keys the retained tables spill L1/L2, so
/// the affine cache's smaller per-key gather footprint (Phase 1c) can show up —
/// unlike `distinct_4`, whose 4 tables fit L1. `HotKeyCache` vs `NullKeyCache`,
/// Zip215, msg_len 1.
fn bench_hot_keys_large(c: &mut Criterion) {
    let mut group = c.benchmark_group("hot_keys/large_distinct");
    for n in [256usize, 1024] {
        let cases = generate_hot_keys(n, n, MsgLen::Fixed(1));
        let inputs = inputs_of(&cases);
        group.throughput(Throughput::Elements(n as u64));

        bench_ours_nocache(
            &mut group,
            "ed25519_simd_nullcache/zip215",
            VerifyPolicy::Zip215,
            n,
            &inputs,
        );
        bench_ours_hot_key_cache(
            &mut group,
            "ed25519_simd_hotcache/zip215",
            VerifyPolicy::Zip215,
            n,
            n,
            &inputs,
        );
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_distinct_keys_len1,
    bench_distinct_keys_len1024,
    bench_distinct_keys_mixed_len,
    bench_garbage_25,
    bench_garbage_50,
    bench_hot_keys_4,
    bench_hot_keys_large,
    bench_hot_keys_churn
);
criterion_main!(benches);
