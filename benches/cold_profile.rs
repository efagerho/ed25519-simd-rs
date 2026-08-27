//! Plain (non-criterion) harness for profiling the cold `NullKeyCache` path.
//! Build: `cargo bench --bench cold_profile --no-run`
//! Profile: `perf record -g <binary> [policy] [keys] [iters] [msglen|mixed] [invalid_pct] [invalid_mode]`

use std::time::Instant;

use curve25519::ed_sigs::{SigningKey, VerificationKeyBytes};
use ed25519_simd::{NullKeyCache, Verifier, VerifyInput, VerifyPolicy};
use rand::{RngCore, SeedableRng, rngs::StdRng};

fn signing_key_from_index(index: u64) -> SigningKey {
    let mut seed = [0u8; 32];
    seed[..8].copy_from_slice(&index.to_le_bytes());
    SigningKey::from(seed)
}

#[derive(Clone, Copy)]
enum MsgLenArg {
    Fixed(usize),
    Mixed,
}

#[derive(Clone, Copy)]
enum InvalidMode {
    WellFormed,
    Malformed,
}

impl InvalidMode {
    fn label(self) -> &'static str {
        match self {
            Self::WellFormed => "wellformed",
            Self::Malformed => "malformed",
        }
    }
}

const USAGE: &str = "usage: cold_profile [zip215|dalek] [keys] [iters] \
                     [msglen|mixed] [invalid_pct] [wellformed|malformed]";

fn usage_error(message: &str) -> ! {
    eprintln!("error: {message}\n{USAGE}");
    std::process::exit(2);
}

fn usize_arg(args: &[String], index: usize, default: usize, name: &str) -> usize {
    args.get(index).map_or(default, |value| {
        value
            .parse()
            .unwrap_or_else(|_| usage_error(&format!("invalid {name}: {value}")))
    })
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    // `cargo test --all-targets` runs this as a plain binary; a one-shot timing
    // would read as a measurement, so bail instead.
    if args.len() == 1 {
        eprintln!("{USAGE}");
        return;
    }
    if args.len() > 7 {
        usage_error("too many arguments");
    }

    let policy = match args.get(1).map(String::as_str) {
        Some("zip215") => VerifyPolicy::Zip215,
        Some("dalek") => VerifyPolicy::Dalek,
        Some(value) => usage_error(&format!("invalid policy: {value}")),
        None => unreachable!(),
    };
    let keys = usize_arg(&args, 2, 512, "key count");
    let iters = usize_arg(&args, 3, 4000, "iteration count");
    if keys == 0 || iters == 0 {
        usage_error("key and iteration counts must be nonzero");
    }
    let msglen_arg = match args.get(4).map(String::as_str) {
        Some("mixed") => MsgLenArg::Mixed,
        Some(_) => MsgLenArg::Fixed(usize_arg(&args, 4, 1, "message length")),
        None => MsgLenArg::Fixed(1),
    };
    let invalid_pct = usize_arg(&args, 5, 0, "invalid percentage");
    if invalid_pct > 100 {
        usage_error("invalid percentage must be between 0 and 100");
    }
    let invalid_mode = match args.get(6).map(String::as_str) {
        Some("wellformed") | None => InvalidMode::WellFormed,
        Some("malformed") => InvalidMode::Malformed,
        Some(value) => usage_error(&format!("invalid invalid-mode: {value}")),
    };

    let mut rng = StdRng::seed_from_u64(0x5eed_1234);
    let mut messages: Vec<Vec<u8>> = Vec::with_capacity(keys);
    let mut pks = Vec::with_capacity(keys);
    let mut sigs = Vec::with_capacity(keys);
    for i in 0..keys {
        let sk = signing_key_from_index(i as u64);
        let pk = <[u8; 32]>::from(VerificationKeyBytes::from(&sk));
        let msglen = match msglen_arg {
            MsgLenArg::Fixed(l) => l,
            MsgLenArg::Mixed => (rng.next_u64() % 257) as usize,
        };
        let msg = vec![(i & 0xff) as u8; msglen];
        let sig = sk.sign(&msg).to_bytes();
        pks.push(pk);
        sigs.push(sig);
        messages.push(msg);
    }
    let mut corrupt_rng = StdRng::seed_from_u64(0x9e37_79b9_7f4a_7c15);
    for (message, signature) in messages.iter_mut().zip(sigs.iter_mut()) {
        if corrupt_rng.next_u64() % 100 < invalid_pct as u64 {
            match invalid_mode {
                InvalidMode::WellFormed => {
                    if message.is_empty() {
                        message.push(1);
                    } else {
                        message[0] ^= 1;
                    }
                }
                InvalidMode::Malformed => signature[32..].fill(0xff),
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
        "{policy:?} keys={keys} iters={iters} msglen={msglen_label} \
         invalid={invalid_pct}%/{} accepted={accepted} \
         total={:.2}s  {:.1} ns/sig  {:.0} sigs/s",
        invalid_mode.label(),
        elapsed.as_secs_f64(),
        per_sig_ns,
        1e9 / per_sig_ns
    );
}
