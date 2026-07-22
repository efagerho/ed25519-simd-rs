//! Lean (non-criterion) harness for the hot-key cache path — the `cold_profile`
//! analogue for `HotKeyCache`. Deliberately links nothing beyond the crate so
//! the instruction-fetch environment stays production-representative.
//!
//! Args: [policy] [keys] [hot_key_count] [cap] [iters] [msglen]
//!   cap = 0 means unbounded; cap > 0 bounds retention (churn scenarios).

use std::time::Instant;

use curve25519::ed_sigs::{SigningKey, VerificationKeyBytes};
use ed25519_simd::{HotKeyCache, Verifier, VerifyInput, VerifyPolicy};

fn signing_key_from_index(index: u64) -> SigningKey {
    let mut seed = [0u8; 32];
    seed[..8].copy_from_slice(&index.to_le_bytes());
    SigningKey::from(seed)
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

enum MsgLenArg {
    Fixed(usize),
    Mixed,
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let policy = match args.get(1).map(String::as_str) {
        Some("dalek") => VerifyPolicy::Dalek,
        _ => VerifyPolicy::Zip215,
    };
    let keys: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(512);
    let hot_key_count: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(4);
    let cap: usize = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(0);
    let iters: usize = args.get(5).and_then(|s| s.parse().ok()).unwrap_or(4000);
    let msglen_arg = match args.get(6).map(String::as_str) {
        Some("mixed") => MsgLenArg::Mixed,
        Some(s) => MsgLenArg::Fixed(s.parse().unwrap_or(1)),
        None => MsgLenArg::Fixed(1),
    };

    // `keys` inputs drawn from `hot_key_count` distinct signing keys, cycled —
    // matches `generate_hot_keys` in the criterion comparison bench.
    let signers: Vec<SigningKey> = (0..hot_key_count.max(1))
        .map(|i| signing_key_from_index(i as u64))
        .collect();

    let mut rng = SplitMix(0x5eed_1234);
    let mut messages: Vec<Vec<u8>> = Vec::with_capacity(keys);
    let mut pks = Vec::with_capacity(keys);
    let mut sigs = Vec::with_capacity(keys);
    for i in 0..keys {
        let sk = &signers[i % signers.len()];
        let pk = <[u8; 32]>::from(VerificationKeyBytes::from(sk));
        let msglen = match msglen_arg {
            MsgLenArg::Fixed(l) => l,
            MsgLenArg::Mixed => (rng.next() % 257) as usize,
        };
        let msg = vec![(i & 0xff) as u8; msglen];
        let sig = sk.sign(&msg).to_bytes();
        pks.push(pk);
        sigs.push(sig);
        messages.push(msg);
    }

    let inputs: Vec<VerifyInput> = (0..keys)
        .map(|i| VerifyInput {
            public_key: pks[i],
            signature: sigs[i],
            message: &messages[i],
        })
        .collect();

    let cache = if cap == 0 {
        HotKeyCache::new()
    } else {
        HotKeyCache::with_capacity(cap)
    };
    let mut verifier = Verifier::with_cache(policy, cache);
    let mut out = vec![false; inputs.len()];
    let mut accepted = 0u64;
    // Warm the cache so steady-state hit behaviour is what gets timed.
    verifier.verify_batch(&inputs, &mut out);
    verifier.verify_batch(&inputs, &mut out);

    let start = Instant::now();
    for _ in 0..iters {
        verifier.verify_batch(&inputs, &mut out);
        accepted += out.iter().filter(|&&b| b).count() as u64;
    }
    let elapsed = start.elapsed();

    let msglen_label = match msglen_arg {
        MsgLenArg::Fixed(l) => l.to_string(),
        MsgLenArg::Mixed => "mixed".to_string(),
    };
    let total_sigs = (iters * keys) as f64;
    let per_sig_ns = elapsed.as_nanos() as f64 / total_sigs;
    eprintln!(
        "{policy:?} keys={keys} hot={hot_key_count} cap={cap} iters={iters} \
         msglen={msglen_label} accepted={accepted} total={:.2}s  {:.1} ns/sig  {:.0} sigs/s",
        elapsed.as_secs_f64(),
        per_sig_ns,
        1e9 / per_sig_ns
    );
}
