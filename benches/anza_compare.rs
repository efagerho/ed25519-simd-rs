use core::convert::TryFrom;
use std::hint::black_box;

use criterion::{
    BenchmarkGroup, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main,
    measurement::WallTime,
};
use curve25519::ed_sigs::{Signature, SigningKey, VerificationKey, VerificationKeyBytes, batch};
use ed25519_simd::{NullKeyCache, Verifier, VerifyInput, VerifyPolicy};

const SIZES: [usize; 4] = [8, 16, 32, 64];

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

fn distinct_keys(cases: &[Owned]) -> Vec<[u8; 32]> {
    cases.iter().map(|c| c.pk).collect()
}

fn anza_batch_zip215(inputs: &[VerifyInput<'_>]) -> bool {
    let mut batch = batch::Verifier::new();
    for input in inputs {
        let vk_bytes = VerificationKeyBytes::from(input.public_key);
        let sig = Signature::from(input.signature);
        batch.queue((vk_bytes, sig, input.message));
    }
    batch.verify(rand::thread_rng()).is_ok()
}

fn anza_dalek_loop(inputs: &[VerifyInput<'_>]) -> bool {
    inputs.iter().all(|input| {
        let vk_bytes = VerificationKeyBytes::from(input.public_key);
        let sig = Signature::from(input.signature);
        VerificationKey::try_from(vk_bytes)
            .and_then(|vk| vk.verify_dalek(&sig, input.message))
            .is_ok()
    })
}

fn bench_ours(
    group: &mut BenchmarkGroup<'_, WallTime>,
    name: &str,
    policy: VerifyPolicy,
    n: usize,
    inputs: &[VerifyInput<'_>],
    preload: &[[u8; 32]],
) {
    group.bench_with_input(BenchmarkId::new(name, n), &n, |b, _| {
        let mut verifier = Verifier::with_policy(policy);
        verifier.preload_public_keys(preload);
        let mut out = vec![false; inputs.len()];
        b.iter(|| {
            verifier.verify_batch(black_box(inputs), &mut out);
            black_box(out.iter().all(|accepted| *accepted))
        })
    });
}

/// Cold path: every batch re-decodes all keys.
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

fn bench_scenario(c: &mut Criterion, group_name: &str, msg_len: MsgLen) {
    let mut group = c.benchmark_group(group_name);
    for n in SIZES {
        let cases = generate_distinct_keys(n, msg_len);
        let inputs = inputs_of(&cases);
        let preload = distinct_keys(&cases);
        group.throughput(Throughput::Elements(n as u64));

        bench_ours(
            &mut group,
            "ed25519_simd/zip215",
            VerifyPolicy::Zip215,
            n,
            &inputs,
            &preload,
        );
        group.bench_with_input(BenchmarkId::new("anza/zip215_batch", n), &n, |b, _| {
            b.iter(|| anza_batch_zip215(black_box(&inputs)))
        });

        bench_ours(
            &mut group,
            "ed25519_simd/dalek",
            VerifyPolicy::Dalek,
            n,
            &inputs,
            &preload,
        );
        group.bench_with_input(BenchmarkId::new("anza/dalek_loop", n), &n, |b, _| {
            b.iter(|| anza_dalek_loop(black_box(&inputs)))
        });

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

        bench_ours(
            &mut group,
            "ed25519_simd/zip215",
            VerifyPolicy::Zip215,
            n,
            &inputs,
            &[],
        );
        bench_ours(
            &mut group,
            "ed25519_simd/dalek",
            VerifyPolicy::Dalek,
            n,
            &inputs,
            &[],
        );
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
        group.bench_with_input(BenchmarkId::new("anza/dalek_loop", n), &n, |b, _| {
            b.iter(|| anza_dalek_loop(black_box(&inputs)))
        });
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

criterion_group!(
    benches,
    bench_distinct_keys_len1,
    bench_distinct_keys_len1024,
    bench_distinct_keys_mixed_len,
    bench_garbage_25,
    bench_garbage_50
);
criterion_main!(benches);
