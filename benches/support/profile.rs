//! Shared setup for the four configuration-specific profiling binaries.

use std::time::Instant;

use curve25519::ed_sigs::{SigningKey, VerificationKeyBytes};
use ed25519_simd::{HotKeyCache, NullKeyCache, Verifier, VerifyInput, VerifyPolicy};
use rand::{RngCore, SeedableRng, rngs::StdRng};

fn policy<const DALEK: bool>() -> VerifyPolicy {
    if DALEK {
        VerifyPolicy::Dalek
    } else {
        VerifyPolicy::Zip215
    }
}

fn signing_key_from_index(index: u64) -> SigningKey {
    let mut seed = [0u8; 32];
    seed[..8].copy_from_slice(&index.to_le_bytes());
    SigningKey::from(seed)
}

fn usage_error(message: &str, usage: &str) -> ! {
    eprintln!("error: {message}\n{usage}");
    std::process::exit(2);
}

fn usize_arg(args: &[String], index: usize, default: usize, name: &str, usage: &str) -> usize {
    args.get(index).map_or(default, |value| {
        value
            .parse()
            .unwrap_or_else(|_| usage_error(&format!("invalid {name}: {value}"), usage))
    })
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

pub fn run_cold<const DALEK: bool>() {
    let args: Vec<String> = std::env::args().collect();
    let usage = format!(
        "usage: {} [keys] [iters] [msglen|mixed] [invalid_pct] \
         [wellformed|malformed]",
        args[0]
    );
    // `cargo test --all-targets` runs this as a plain binary; a one-shot timing
    // would read as a measurement, so bail instead.
    if args.len() == 1 {
        eprintln!("{usage}");
        return;
    }
    if args.len() > 6 {
        usage_error("too many arguments", &usage);
    }

    let keys = usize_arg(&args, 1, 512, "key count", &usage);
    let iters = usize_arg(&args, 2, 4000, "iteration count", &usage);
    if keys == 0 || iters == 0 {
        usage_error("key and iteration counts must be nonzero", &usage);
    }
    let msglen_arg = match args.get(3).map(String::as_str) {
        Some("mixed") => MsgLenArg::Mixed,
        Some(_) => MsgLenArg::Fixed(usize_arg(&args, 3, 1, "message length", &usage)),
        None => MsgLenArg::Fixed(1),
    };
    let invalid_pct = usize_arg(&args, 4, 0, "invalid percentage", &usage);
    if invalid_pct > 100 {
        usage_error("invalid percentage must be between 0 and 100", &usage);
    }
    let invalid_mode = match args.get(5).map(String::as_str) {
        Some("wellformed") | None => InvalidMode::WellFormed,
        Some("malformed") => InvalidMode::Malformed,
        Some(value) => usage_error(&format!("invalid invalid-mode: {value}"), &usage),
    };

    let mut rng = StdRng::seed_from_u64(0x5eed_1234);
    let mut messages: Vec<Vec<u8>> = Vec::with_capacity(keys);
    let mut public_keys = Vec::with_capacity(keys);
    let mut signatures = Vec::with_capacity(keys);
    for i in 0..keys {
        let signing_key = signing_key_from_index(i as u64);
        let public_key = <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key));
        let message_len = match msglen_arg {
            MsgLenArg::Fixed(len) => len,
            MsgLenArg::Mixed => (rng.next_u64() % 257) as usize,
        };
        let message = vec![(i & 0xff) as u8; message_len];
        let signature = signing_key.sign(&message).to_bytes();
        public_keys.push(public_key);
        signatures.push(signature);
        messages.push(message);
    }
    let mut corrupt_rng = StdRng::seed_from_u64(0x9e37_79b9_7f4a_7c15);
    for (message, signature) in messages.iter_mut().zip(signatures.iter_mut()) {
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

    let inputs: Vec<VerifyInput<'_>> = (0..keys)
        .map(|i| VerifyInput {
            public_key: public_keys[i],
            signature: signatures[i],
            message: &messages[i],
        })
        .collect();

    let selected_policy = policy::<DALEK>();
    let mut verifier = Verifier::with_cache(selected_policy, NullKeyCache::new());
    let mut out = vec![false; inputs.len()];
    let mut accepted = 0u64;
    verifier.verify_batch(&inputs, &mut out);

    let start = Instant::now();
    for _ in 0..iters {
        verifier.verify_batch(&inputs, &mut out);
        accepted += out.iter().filter(|&&accepted| accepted).count() as u64;
    }
    let elapsed = start.elapsed();

    let msglen_label = match msglen_arg {
        MsgLenArg::Fixed(len) => len.to_string(),
        MsgLenArg::Mixed => "mixed".to_owned(),
    };
    let total_signatures = (iters * keys) as f64;
    let per_signature_ns = elapsed.as_nanos() as f64 / total_signatures;
    eprintln!(
        "{selected_policy:?} keys={keys} iters={iters} msglen={msglen_label} \
         invalid={invalid_pct}%/{} accepted={accepted} \
         total={:.2}s  {:.1} ns/sig  {:.0} sigs/s",
        invalid_mode.label(),
        elapsed.as_secs_f64(),
        per_signature_ns,
        1e9 / per_signature_ns
    );
}

pub fn run_hot<const DALEK: bool>() {
    let args: Vec<String> = std::env::args().collect();
    let usage = format!("usage: {} [keys] [iters] [hot_keys] [msglen]", args[0]);
    if args.len() == 1 {
        eprintln!("{usage}");
        return;
    }
    if args.len() > 5 {
        usage_error("too many arguments", &usage);
    }

    let keys = usize_arg(&args, 1, 512, "key count", &usage);
    let iters = usize_arg(&args, 2, 4000, "iteration count", &usage);
    let hot_keys = usize_arg(&args, 3, 4, "hot-key count", &usage);
    let message_len = usize_arg(&args, 4, 1, "message length", &usage);
    if keys == 0 || iters == 0 || hot_keys == 0 {
        usage_error("key and iteration counts must be nonzero", &usage);
    }

    let mut messages = Vec::with_capacity(keys);
    let mut public_keys = Vec::with_capacity(keys);
    let mut signatures = Vec::with_capacity(keys);
    for i in 0..keys {
        let signing_key = signing_key_from_index((i % hot_keys) as u64);
        let message = vec![(i & 0xff) as u8; message_len];
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

    let selected_policy = policy::<DALEK>();
    let mut verifier = Verifier::with_cache(selected_policy, HotKeyCache::with_capacity(hot_keys));
    let mut out = vec![false; keys];
    verifier.verify_batch(&inputs, &mut out);

    let start = Instant::now();
    let mut accepted = 0u64;
    for _ in 0..iters {
        verifier.verify_batch(&inputs, &mut out);
        accepted += out.iter().filter(|&&accepted| accepted).count() as u64;
    }
    let elapsed = start.elapsed();
    let per_signature_ns = elapsed.as_nanos() as f64 / (keys * iters) as f64;
    eprintln!(
        "{selected_policy:?} keys={keys} iters={iters} hot_keys={hot_keys} \
         msglen={message_len} accepted={accepted} total={:.2}s  \
         {:.1} ns/sig  {:.0} sigs/s",
        elapsed.as_secs_f64(),
        per_signature_ns,
        1e9 / per_signature_ns,
    );
}
