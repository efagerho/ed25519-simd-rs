use core::convert::TryFrom;
use std::hint::black_box;

use criterion::{
    BenchmarkGroup, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main,
    measurement::WallTime,
};
use curve25519::ed_sigs::{Signature, SigningKey, VerificationKey, VerificationKeyBytes, batch};
use ed25519_dalek::{
    Signature as DalekSignature, VerifyingKey as DalekVerifyingKey,
    verify_batch as dalek_verify_batch,
};
use ed25519_simd::{NullKeyCache, Verifier, VerifyInput, VerifyPolicy};
use openssl::{
    pkey::{Id as OpenSslId, PKey, Public as OpenSslPublic},
    sign::Verifier as OpenSslVerifier,
};
use sodiumoxide::crypto::sign::ed25519::{
    PublicKey as SodiumPublicKey, Signature as SodiumSignature, verify_detached as sodium_verify,
};

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

fn solana_ed25519_batch_zip215(inputs: &[VerifyInput<'_>]) -> bool {
    let mut batch = batch::Verifier::new();
    for input in inputs {
        let vk_bytes = VerificationKeyBytes::from(input.public_key);
        let sig = Signature::from(input.signature);
        batch.queue((vk_bytes, sig, input.message));
    }
    batch.verify(rand::thread_rng()).is_ok()
}

fn solana_ed25519_dalek_loop(inputs: &[VerifyInput<'_>]) -> bool {
    inputs.iter().all(|input| {
        let vk_bytes = VerificationKeyBytes::from(input.public_key);
        let sig = Signature::from(input.signature);
        VerificationKey::try_from(vk_bytes)
            .and_then(|vk| vk.verify_dalek(&sig, input.message))
            .is_ok()
    })
}

struct DalekBatchInputs<'a> {
    messages: Vec<&'a [u8]>,
    signatures: Vec<DalekSignature>,
    verifying_keys: Vec<DalekVerifyingKey>,
}

fn dalek_batch_inputs<'msg>(inputs: &[VerifyInput<'msg>]) -> DalekBatchInputs<'msg> {
    let messages = inputs.iter().map(|input| input.message).collect();
    let signatures = inputs
        .iter()
        .map(|input| DalekSignature::from_bytes(&input.signature))
        .collect();
    let verifying_keys = inputs
        .iter()
        .map(|input| DalekVerifyingKey::from_bytes(&input.public_key).unwrap())
        .collect();
    DalekBatchInputs {
        messages,
        signatures,
        verifying_keys,
    }
}

fn dalek_batch(batch: &DalekBatchInputs<'_>) -> bool {
    dalek_verify_batch(&batch.messages, &batch.signatures, &batch.verifying_keys).is_ok()
}

fn aws_lc_keys(inputs: &[VerifyInput<'_>]) -> Vec<aws_lc_rs::signature::ParsedPublicKey> {
    inputs
        .iter()
        .map(|input| {
            aws_lc_rs::signature::ParsedPublicKey::new(
                &aws_lc_rs::signature::ED25519,
                input.public_key,
            )
            .unwrap()
        })
        .collect()
}

fn aws_lc_loop(inputs: &[VerifyInput<'_>], keys: &[aws_lc_rs::signature::ParsedPublicKey]) -> bool {
    inputs
        .iter()
        .zip(keys)
        .all(|(input, key)| key.verify_sig(input.message, &input.signature).is_ok())
}

fn ring_keys(inputs: &[VerifyInput<'_>]) -> Vec<ring::signature::UnparsedPublicKey<[u8; 32]>> {
    inputs
        .iter()
        .map(|input| {
            ring::signature::UnparsedPublicKey::new(&ring::signature::ED25519, input.public_key)
        })
        .collect()
}

fn ring_loop(
    inputs: &[VerifyInput<'_>],
    keys: &[ring::signature::UnparsedPublicKey<[u8; 32]>],
) -> bool {
    inputs
        .iter()
        .zip(keys)
        .all(|(input, key)| key.verify(input.message, &input.signature).is_ok())
}

fn sodium_inputs(inputs: &[VerifyInput<'_>]) -> (Vec<SodiumPublicKey>, Vec<SodiumSignature>) {
    sodiumoxide::init().expect("failed to initialize libsodium");
    let keys = inputs
        .iter()
        .map(|input| SodiumPublicKey::from_slice(&input.public_key).unwrap())
        .collect();
    let signatures = inputs
        .iter()
        .map(|input| SodiumSignature::from_bytes(&input.signature).unwrap())
        .collect();
    (keys, signatures)
}

fn sodium_loop(
    inputs: &[VerifyInput<'_>],
    keys: &[SodiumPublicKey],
    signatures: &[SodiumSignature],
) -> bool {
    inputs
        .iter()
        .zip(keys)
        .zip(signatures)
        .all(|((input, key), signature)| sodium_verify(signature, input.message, key))
}

fn openssl_keys(inputs: &[VerifyInput<'_>]) -> Vec<PKey<OpenSslPublic>> {
    inputs
        .iter()
        .map(|input| {
            PKey::public_key_from_raw_bytes(&input.public_key, OpenSslId::ED25519).unwrap()
        })
        .collect()
}

fn openssl_loop(inputs: &[VerifyInput<'_>], keys: &[PKey<OpenSslPublic>]) -> bool {
    inputs.iter().zip(keys).all(|(input, key)| {
        OpenSslVerifier::new_without_digest(key)
            .and_then(|mut verifier| verifier.verify_oneshot(&input.signature, input.message))
            .unwrap_or(false)
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

        let dalek_batch_inputs = dalek_batch_inputs(&inputs);
        group.bench_with_input(BenchmarkId::new("ed25519_dalek/batch", n), &n, |b, _| {
            b.iter(|| dalek_batch(black_box(&dalek_batch_inputs)))
        });

        let aws_lc_keys = aws_lc_keys(&inputs);
        group.bench_with_input(BenchmarkId::new("aws_lc_rs/parsed_loop", n), &n, |b, _| {
            b.iter(|| aws_lc_loop(black_box(&inputs), black_box(&aws_lc_keys)))
        });

        let ring_keys = ring_keys(&inputs);
        group.bench_with_input(BenchmarkId::new("ring/unparsed_loop", n), &n, |b, _| {
            b.iter(|| ring_loop(black_box(&inputs), black_box(&ring_keys)))
        });

        let (sodium_keys, sodium_signatures) = sodium_inputs(&inputs);
        group.bench_with_input(BenchmarkId::new("sodiumoxide/loop", n), &n, |b, _| {
            b.iter(|| {
                sodium_loop(
                    black_box(&inputs),
                    black_box(&sodium_keys),
                    black_box(&sodium_signatures),
                )
            })
        });

        let openssl_keys = openssl_keys(&inputs);
        group.bench_with_input(BenchmarkId::new("openssl/loop", n), &n, |b, _| {
            b.iter(|| openssl_loop(black_box(&inputs), black_box(&openssl_keys)))
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
        let dalek_batch_inputs = dalek_batch_inputs(&inputs);
        group.bench_with_input(BenchmarkId::new("ed25519_dalek/batch", n), &n, |b, _| {
            b.iter(|| dalek_batch(black_box(&dalek_batch_inputs)))
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

criterion_group!(
    benches,
    bench_distinct_keys_len1,
    bench_distinct_keys_len1024,
    bench_distinct_keys_mixed_len,
    bench_garbage_25,
    bench_garbage_50
);
criterion_main!(benches);
