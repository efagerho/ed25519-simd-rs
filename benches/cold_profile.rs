//! Plain (non-criterion) harness for profiling the cold `NullKeyCache` path.
//! Build: `cargo bench --bench cold_profile --no-run`
//! Profile: `perf record -g <binary> [policy] [keys] [iters] [msglen|mixed] [invalid_pct]`

use std::time::Instant;

use curve25519::ed_sigs::{SigningKey, VerificationKeyBytes};
use ed25519_simd::{NullKeyCache, Verifier, VerifyInput, VerifyPolicy};

fn signing_key_from_index(index: u64) -> SigningKey {
    let mut seed = [0u8; 32];
    seed[..8].copy_from_slice(&index.to_le_bytes());
    SigningKey::from(seed)
}

/// Matches `MsgLen::Mixed` in benches/solana_ed25519_compare.rs: a uniform
/// random length in [0, 257) per signature.
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
    let iters: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(4000);
    let msglen_arg = match args.get(4).map(String::as_str) {
        Some("mixed") => MsgLenArg::Mixed,
        Some(s) => MsgLenArg::Fixed(s.parse().unwrap_or(1)),
        None => MsgLenArg::Fixed(1),
    };

    let mut rng = SplitMix(0x5eed_1234);
    let mut messages: Vec<Vec<u8>> = Vec::with_capacity(keys);
    let mut pks = Vec::with_capacity(keys);
    let mut sigs = Vec::with_capacity(keys);
    for i in 0..keys {
        let sk = signing_key_from_index(i as u64);
        let pk = <[u8; 32]>::from(VerificationKeyBytes::from(&sk));
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
    let invalid_pct: u64 = args.get(5).and_then(|s| s.parse().ok()).unwrap_or(0);
    let mut st = 0x9e37_79b9_7f4a_7c15u64;
    for sig in sigs.iter_mut() {
        st = st.wrapping_mul(0xd1342543de82ef95).wrapping_add(1);
        if (st >> 40) % 100 < invalid_pct {
            for (j, b) in sig.iter_mut().enumerate() {
                *b = (st >> (j % 8 * 8)) as u8;
            }
        }
    }

    let inputs: Vec<VerifyInput> = (0..keys)
        .map(|i| VerifyInput {
            public_key: pks[i],
            signature: sigs[i],
            message: &messages[i],
        })
        .collect();

    let mut verifier = Verifier::with_cache(policy, NullKeyCache::new());
    let mut out = vec![false; inputs.len()];
    let mut accepted = 0u64;
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
        "{policy:?} keys={keys} iters={iters} msglen={msglen_label} accepted={accepted} \
         total={:.2}s  {:.1} ns/sig  {:.0} sigs/s",
        elapsed.as_secs_f64(),
        per_sig_ns,
        1e9 / per_sig_ns
    );
}
