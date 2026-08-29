//! Plain profiling harness for steady-state `HotKeyCache` hits.
//! Build: `cargo bench --bench hot_profile --no-run`
//! Run: `hot_profile [zip215|dalek] [keys] [iters] [hot_keys] [msglen]`

use std::time::Instant;

use curve25519::ed_sigs::{SigningKey, VerificationKeyBytes};
use ed25519_simd::{HotKeyCache, Verifier, VerifyInput, VerifyPolicy};

fn signing_key_from_index(index: u64) -> SigningKey {
    let mut seed = [0u8; 32];
    seed[..8].copy_from_slice(&index.to_le_bytes());
    SigningKey::from(seed)
}

fn parse_usize(args: &[String], index: usize, default: usize) -> usize {
    args.get(index)
        .map_or(default, |value| value.parse().expect("integer argument"))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() == 1 {
        eprintln!("usage: hot_profile [zip215|dalek] [keys] [iters] [hot_keys] [msglen]");
        return;
    }
    let policy = match args.get(1).map(String::as_str) {
        Some("zip215") => VerifyPolicy::Zip215,
        Some("dalek") => VerifyPolicy::Dalek,
        _ => panic!("policy must be zip215 or dalek"),
    };
    let keys = parse_usize(&args, 2, 512);
    let iters = parse_usize(&args, 3, 4000);
    let hot_keys = parse_usize(&args, 4, 4);
    let msglen = parse_usize(&args, 5, 1);
    assert!(keys > 0 && iters > 0 && hot_keys > 0);

    let mut messages = Vec::with_capacity(keys);
    let mut public_keys = Vec::with_capacity(keys);
    let mut signatures = Vec::with_capacity(keys);
    for i in 0..keys {
        let signing_key = signing_key_from_index((i % hot_keys) as u64);
        let message = vec![(i & 0xff) as u8; msglen];
        public_keys.push(<[u8; 32]>::from(VerificationKeyBytes::from(&signing_key)));
        signatures.push(signing_key.sign(&message).to_bytes());
        messages.push(message);
    }
    let inputs: Vec<VerifyInput<'_>> = (0..keys)
        .map(|i| VerifyInput {
            public_key: public_keys[i],
            signature: signatures[i],
            message: &messages[i],
        })
        .collect();

    let mut verifier = Verifier::with_cache(policy, HotKeyCache::with_capacity(hot_keys));
    let mut out = vec![false; keys];
    verifier.verify_batch(&inputs, &mut out);

    let start = Instant::now();
    let mut accepted = 0u64;
    for _ in 0..iters {
        verifier.verify_batch(&inputs, &mut out);
        accepted += out.iter().filter(|&&value| value).count() as u64;
    }
    let elapsed = start.elapsed();
    let per_signature_ns = elapsed.as_nanos() as f64 / (keys * iters) as f64;
    eprintln!(
        "{policy:?} keys={keys} iters={iters} hot_keys={hot_keys} msglen={msglen} \
         accepted={accepted} total={:.2}s  {:.1} ns/sig  {:.0} sigs/s",
        elapsed.as_secs_f64(),
        per_signature_ns,
        1e9 / per_signature_ns,
    );
}
