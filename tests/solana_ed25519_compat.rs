//! Acceptance-set differential tests against solana-ed25519's Ed25519 verifier.
//!
//! Covers ZIP-215 vs `verify_zebra`/`batch::Verifier` and Dalek vs `verify_dalek`.

use core::convert::TryFrom;

use curve25519::ed_sigs::{Signature, SigningKey, VerificationKey, VerificationKeyBytes, batch};
use ed25519_simd::{KeyCache, NullKeyCache, Verifier, VerifyInput, VerifyPolicy};

fn ours_single(input: VerifyInput<'_>) -> bool {
    let mut verifier = Verifier::with_cache(VerifyPolicy::default(), NullKeyCache::new());
    let mut out = [false];
    verifier.verify_batch(&[input], &mut out);
    out[0]
}

fn solana_ed25519_verify_zebra(public_key: [u8; 32], signature: [u8; 64], message: &[u8]) -> bool {
    let vk_bytes = VerificationKeyBytes::from(public_key);
    let sig = Signature::from(signature);
    VerificationKey::try_from(vk_bytes)
        .and_then(|vk| vk.verify_zebra(&sig, message))
        .is_ok()
}

fn solana_ed25519_verify_dalek(public_key: [u8; 32], signature: [u8; 64], message: &[u8]) -> bool {
    let vk_bytes = VerificationKeyBytes::from(public_key);
    let sig = Signature::from(signature);
    VerificationKey::try_from(vk_bytes)
        .and_then(|vk| vk.verify_dalek(&sig, message))
        .is_ok()
}

fn ours_policy(
    public_key: [u8; 32],
    signature: [u8; 64],
    message: &[u8],
    policy: ed25519_simd::VerifyPolicy,
) -> bool {
    let mut verifier = Verifier::with_policy(policy);
    let mut out = [false];
    verifier.verify_batch(
        &[VerifyInput {
            public_key,
            signature,
            message,
        }],
        &mut out,
    );
    out[0]
}

fn hx(s: &str) -> [u8; 32] {
    let mut out = [0u8; 32];
    let b = s.as_bytes();
    for i in 0..32 {
        let hi = (b[2 * i] as char).to_digit(16).unwrap() as u8;
        let lo = (b[2 * i + 1] as char).to_digit(16).unwrap() as u8;
        out[i] = (hi << 4) | lo;
    }
    out
}

fn solana_ed25519_verify_batch(inputs: &[VerifyInput<'_>]) -> bool {
    let mut batch = batch::Verifier::new();
    for input in inputs {
        let vk_bytes = VerificationKeyBytes::from(input.public_key);
        let sig = Signature::from(input.signature);
        batch.queue((vk_bytes, sig, input.message));
    }
    batch.verify(rand::thread_rng()).is_ok()
}

struct Lcg(u64);
impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    fn fill(&mut self, buf: &mut [u8]) {
        for chunk in buf.chunks_mut(8) {
            let bytes = self.next_u64().to_le_bytes();
            chunk.copy_from_slice(&bytes[..chunk.len()]);
        }
    }
}

fn signing_key_from_index(index: u64) -> SigningKey {
    let mut seed = [0u8; 32];
    seed[..8].copy_from_slice(&index.to_le_bytes());
    SigningKey::from(seed)
}

struct Case {
    public_key: [u8; 32],
    signature: [u8; 64],
    message: Vec<u8>,
}

type SolanaEd25519VerifyFn = fn([u8; 32], [u8; 64], &[u8]) -> bool;

impl Case {
    fn input(&self) -> VerifyInput<'_> {
        VerifyInput {
            public_key: self.public_key,
            signature: self.signature,
            message: &self.message,
        }
    }
}

fn build_corpus(count: usize) -> Vec<Case> {
    let mut rng = Lcg(0x0123_4567_89ab_cdef);
    let mut cases = Vec::with_capacity(count);

    for i in 0..count {
        let kind = i % 5;
        let len = (rng.next_u64() % 300) as usize;
        let mut message = vec![0u8; len];
        rng.fill(&mut message);

        let signing_key = signing_key_from_index(rng.next_u64());
        let public_key = <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key));
        let signature = signing_key.sign(&message).to_bytes();

        let case = match kind {
            0 => Case {
                public_key,
                signature,
                message,
            },
            1 => {
                let mut signature = signature;
                let byte = (rng.next_u64() % 64) as usize;
                signature[byte] ^= 1 << (rng.next_u64() % 8);
                Case {
                    public_key,
                    signature,
                    message,
                }
            }
            2 => {
                if message.is_empty() {
                    message.push(0xff);
                } else {
                    let byte = (rng.next_u64() as usize) % message.len();
                    message[byte] ^= 1 << (rng.next_u64() % 8);
                }
                Case {
                    public_key,
                    signature,
                    message,
                }
            }
            3 => {
                let mut public_key = [0u8; 32];
                rng.fill(&mut public_key);
                Case {
                    public_key,
                    signature,
                    message,
                }
            }
            _ => {
                let mut signature = [0u8; 64];
                rng.fill(&mut signature);
                Case {
                    public_key,
                    signature,
                    message,
                }
            }
        };
        cases.push(case);
    }
    cases
}

#[test]
fn single_verify_matches_solana_ed25519_on_canonical_corpus() {
    let cases = build_corpus(4000);

    let mut verifier = Verifier::new();
    let mut disagreements = 0usize;
    let mut accepted = 0usize;

    for case in &cases {
        let input = case.input();
        let ours = ours_single(input);
        let mut cached_out = [false];
        verifier.verify_batch(&[input], &mut cached_out);
        let ours_cached = cached_out[0];
        let theirs = solana_ed25519_verify_zebra(case.public_key, case.signature, &case.message);

        assert_eq!(ours, ours_cached, "crate stateless vs cached disagree");

        if ours != theirs {
            disagreements += 1;
            eprintln!(
                "DISAGREE pk={:02x?} sig0={:02x} msglen={} ours={} solana-ed25519={}",
                &case.public_key[..4],
                case.signature[0],
                case.message.len(),
                ours,
                theirs
            );
        }
        if ours {
            accepted += 1;
        }
    }

    // Only `kind == 0` (1/5 of the corpus) is always valid; the rest reject.
    // The band catches both false-reject and over-accept regressions.
    let valid_fraction = cases.len() / 5;
    assert!(
        (valid_fraction..=valid_fraction + cases.len() / 50).contains(&accepted),
        "expected about {valid_fraction} accepts, got {accepted}"
    );
    assert_eq!(
        disagreements, 0,
        "crate and solana-ed25519 disagreed on {disagreements} canonical inputs"
    );
}

#[test]
fn null_cache_matches_solana_ed25519() {
    for &size in &[8usize, 12, 16, 32] {
        for trial in 0..4u64 {
            let mut rng = Lcg(0xc01d_0000 + trial * 977 + size as u64);
            let len = (rng.next_u64() % 200) as usize;

            let mut cases: Vec<Case> = Vec::with_capacity(size);
            for _ in 0..size {
                let mut message = vec![0u8; len];
                rng.fill(&mut message);
                let signing_key = signing_key_from_index(rng.next_u64());
                let public_key = <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key));
                let mut signature = signing_key.sign(&message).to_bytes();
                if rng.next_u64().is_multiple_of(4) {
                    let b = (rng.next_u64() % 64) as usize;
                    signature[b] ^= 1 << (rng.next_u64() % 8);
                }
                cases.push(Case {
                    public_key,
                    signature,
                    message,
                });
            }
            let inputs: Vec<VerifyInput<'_>> = cases.iter().map(|c| c.input()).collect();

            let policies: [(VerifyPolicy, SolanaEd25519VerifyFn); 2] = [
                (VerifyPolicy::Zip215, solana_ed25519_verify_zebra),
                (VerifyPolicy::Dalek, solana_ed25519_verify_dalek),
            ];
            for (policy, solana_ed25519) in policies {
                let mut verifier = Verifier::with_cache(policy, NullKeyCache::new());
                let mut out = vec![false; inputs.len()];
                verifier.verify_batch(&inputs, &mut out);
                for (idx, input) in inputs.iter().enumerate() {
                    let theirs = solana_ed25519(input.public_key, input.signature, input.message);
                    assert_eq!(
                        out[idx], theirs,
                        "null-cache {policy:?} element {idx} (size={size}) disagrees with solana-ed25519"
                    );
                }
                assert!(verifier.cache().get(&inputs[0].public_key).is_none());
            }
        }
    }
}

#[test]
fn block_count_bucketed_batches_match_solana_ed25519() {
    let lengths = [
        1usize, 2048, 64, 1024, 2, 1536, 128, 4096, 3, 512, 65, 2047, 4, 256, 112, 3072, 5, 1025,
        63, 2048, 6, 768, 127, 4095, 7, 1537, 48, 1024, 8, 511, 113, 2048, 9, 4096, 64, 1023, 10,
        256, 129, 3071,
    ];
    let mut rng = Lcg(0xb0cc_e7ed_5eed);
    let mut cases = Vec::with_capacity(lengths.len());

    for (idx, &len) in lengths.iter().enumerate() {
        let mut message = vec![0u8; len];
        rng.fill(&mut message);
        let signing_key = signing_key_from_index(idx as u64 + 10_000);
        let public_key = <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key));
        let mut signature = signing_key.sign(&message).to_bytes();
        if idx % 7 == 3 {
            signature[(idx * 11) % 64] ^= 0x40;
        }
        cases.push(Case {
            public_key,
            signature,
            message,
        });
    }

    let inputs: Vec<VerifyInput<'_>> = cases.iter().map(|c| c.input()).collect();
    let policies: [(VerifyPolicy, SolanaEd25519VerifyFn); 2] = [
        (VerifyPolicy::Zip215, solana_ed25519_verify_zebra),
        (VerifyPolicy::Dalek, solana_ed25519_verify_dalek),
    ];

    for (policy, solana_ed25519) in policies {
        let expected: Vec<bool> = inputs
            .iter()
            .map(|input| solana_ed25519(input.public_key, input.signature, input.message))
            .collect();

        let mut cached = Verifier::with_policy(policy);
        let mut cached_out = vec![false; inputs.len()];
        cached.verify_batch(&inputs, &mut cached_out);
        assert_eq!(cached_out, expected, "lru policy={policy:?}");

        let mut cold = Verifier::with_cache(policy, NullKeyCache::new());
        let mut cold_out = vec![false; inputs.len()];
        cold.verify_batch(&inputs, &mut cold_out);
        assert_eq!(cold_out, expected, "null-cache policy={policy:?}");
    }
}

/// Stresses the 8-wide distinct-key decode/table path against solana-ed25519.
#[test]
fn null_cache_decode_build_stress() {
    let mut rng = Lcg(0x5151_5151_5151_5151);
    let mut zip = Verifier::with_cache(VerifyPolicy::Zip215, NullKeyCache::new());
    let mut dalek = Verifier::with_cache(VerifyPolicy::Dalek, NullKeyCache::new());

    for _ in 0..400 {
        let len = (rng.next_u64() % 257) as usize;
        let mut cases: Vec<Case> = Vec::with_capacity(8);
        for _ in 0..8 {
            let mut message = vec![0u8; len];
            rng.fill(&mut message);
            let signing_key = signing_key_from_index(rng.next_u64());
            let public_key = <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key));
            let mut signature = signing_key.sign(&message).to_bytes();
            match rng.next_u64() % 3 {
                0 => signature[(rng.next_u64() % 64) as usize] ^= 1 << (rng.next_u64() % 8),
                1 => message
                    .iter_mut()
                    .for_each(|b| *b ^= (rng.next_u64() & 1) as u8),
                _ => {}
            }
            cases.push(Case {
                public_key,
                signature,
                message,
            });
        }
        let inputs: Vec<VerifyInput<'_>> = cases.iter().map(|c| c.input()).collect();

        let mut out = vec![false; 8];
        zip.verify_batch(&inputs, &mut out);
        for (i, input) in inputs.iter().enumerate() {
            assert_eq!(
                out[i],
                solana_ed25519_verify_zebra(input.public_key, input.signature, input.message),
                "zip215 stress lane {i}"
            );
        }
        dalek.verify_batch(&inputs, &mut out);
        for (i, input) in inputs.iter().enumerate() {
            assert_eq!(
                out[i],
                solana_ed25519_verify_dalek(input.public_key, input.signature, input.message),
                "dalek stress lane {i}"
            );
        }
    }
}

#[test]
fn batch_verify_matches_solana_ed25519() {
    for &size in &[8usize, 9, 16, 31, 32] {
        for trial in 0..6u64 {
            let mut rng = Lcg(0xdead_0000 + trial * 911 + size as u64);
            let uniform = trial % 2 == 0;
            let len = (rng.next_u64() % 200) as usize;

            let mut cases: Vec<Case> = Vec::with_capacity(size);
            let shared_key_index = rng.next_u64();
            for _ in 0..size {
                let mut message = vec![0u8; len];
                rng.fill(&mut message);
                let key_index = if uniform {
                    shared_key_index
                } else {
                    rng.next_u64()
                };
                let signing_key = signing_key_from_index(key_index);
                let public_key = <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key));
                let mut signature = signing_key.sign(&message).to_bytes();
                if rng.next_u64().is_multiple_of(4) {
                    let b = (rng.next_u64() % 64) as usize;
                    signature[b] ^= 1 << (rng.next_u64() % 8);
                }
                cases.push(Case {
                    public_key,
                    signature,
                    message,
                });
            }

            let inputs: Vec<VerifyInput<'_>> = cases.iter().map(|c| c.input()).collect();

            let mut verifier = Verifier::new();
            let keys: Vec<[u8; 32]> = cases.iter().map(|c| c.public_key).collect();
            verifier.preload_public_keys(&keys);
            let mut out = vec![false; inputs.len()];
            verifier.verify_batch(&inputs, &mut out);

            for (idx, input) in inputs.iter().enumerate() {
                let theirs =
                    solana_ed25519_verify_zebra(input.public_key, input.signature, input.message);
                assert_eq!(
                    out[idx], theirs,
                    "batch element {idx} (size={size}, uniform={uniform}) disagrees"
                );
            }

            let all_ok = out.iter().all(|&b| b);
            let solana_ed25519_all_ok = solana_ed25519_verify_batch(&inputs);
            assert_eq!(
                all_ok, solana_ed25519_all_ok,
                "batch-level accept disagrees (size={size}, uniform={uniform})"
            );
        }
    }
}

#[test]
fn batch_dalek_matches_solana_ed25519_simd() {
    use ed25519_simd::VerifyPolicy::Dalek;

    for &size in &[8usize, 16, 24, 31] {
        for trial in 0..6u64 {
            let mut rng = Lcg(0xda1e_0000 + trial * 733 + size as u64);
            let uniform = trial % 2 == 0;
            let len = (rng.next_u64() % 200) as usize;

            let mut cases: Vec<Case> = Vec::with_capacity(size);
            let shared = rng.next_u64();
            for j in 0..size {
                let mut message = vec![0u8; len];
                rng.fill(&mut message);
                let key_index = if uniform { shared } else { rng.next_u64() };
                let signing_key = signing_key_from_index(key_index);
                let public_key = <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key));
                let mut signature = signing_key.sign(&message).to_bytes();
                match rng.next_u64() % 6 {
                    0 => {
                        let b = (rng.next_u64() % 64) as usize;
                        signature[b] ^= 1 << (rng.next_u64() % 8);
                    }
                    1 => {
                        signature[..32].copy_from_slice(&[0u8; 32]);
                    }
                    2 if j == 0 => {
                        let mut r = [0u8; 32];
                        r[0] = 1;
                        signature[..32].copy_from_slice(&r);
                    }
                    _ => {}
                }
                cases.push(Case {
                    public_key,
                    signature,
                    message,
                });
            }

            let inputs: Vec<VerifyInput<'_>> = cases.iter().map(|c| c.input()).collect();
            let mut verifier = Verifier::with_policy(Dalek);
            let keys: Vec<[u8; 32]> = cases.iter().map(|c| c.public_key).collect();
            verifier.preload_public_keys(&keys);
            let mut out = vec![false; inputs.len()];
            verifier.verify_batch(&inputs, &mut out);

            for (idx, input) in inputs.iter().enumerate() {
                let theirs =
                    solana_ed25519_verify_dalek(input.public_key, input.signature, input.message);
                assert_eq!(
                    out[idx], theirs,
                    "dalek batch element {idx} (size={size}, uniform={uniform}) disagrees"
                );
            }
        }
    }
}

#[test]
fn lru_capacity_does_not_evict_current_simd_chunk() {
    let mut cases = Vec::with_capacity(8);
    for i in 0..8 {
        let message = vec![i as u8; 17 + i];
        let signing_key = signing_key_from_index(0xfeed_0000 + i as u64);
        let public_key = <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key));
        let signature = signing_key.sign(&message).to_bytes();
        cases.push(Case {
            public_key,
            signature,
            message,
        });
    }

    let inputs: Vec<VerifyInput<'_>> = cases.iter().map(|case| case.input()).collect();
    let mut verifier = Verifier::with_policy_and_cache_capacity(VerifyPolicy::Zip215, 1);
    let mut out = vec![false; inputs.len()];
    verifier.verify_batch(&inputs, &mut out);

    assert_eq!(out, vec![true; 8]);
    // Exactly 1 (not `<= 1`) proves a key survived rather than nothing caching.
    assert_eq!(verifier.cache().stats().keys, 1);
}

/// Exercises per-lane validity masking across keys, `R`, and `s`.
#[test]
fn per_lane_masking_matches_solana_ed25519_under_heavy_garbage() {
    use ed25519_simd::VerifyPolicy::{Dalek, Zip215};

    for &policy in &[Zip215, Dalek] {
        for &size in &[8usize, 9, 16, 17, 32, 33, 64] {
            for trial in 0..8u64 {
                let mut rng = Lcg(0x6a11_0000 + trial * 1009 + size as u64 * 7 + policy as u64);
                let len = (rng.next_u64() % 96) as usize;

                let mut cases: Vec<Case> = Vec::with_capacity(size);
                for _ in 0..size {
                    let mut message = vec![0u8; len];
                    rng.fill(&mut message);
                    let signing_key = signing_key_from_index(rng.next_u64());
                    let mut public_key = <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key));
                    let mut signature = signing_key.sign(&message).to_bytes();

                    match rng.next_u64() % 10 {
                        0 => rng.fill(&mut public_key),
                        1 => public_key = [0u8; 32],
                        2 => rng.fill(&mut signature[..32]),
                        3 => signature[..32].copy_from_slice(&[0xff; 32]),
                        4 => rng.fill(&mut signature[32..]),
                        5 => signature[32..].copy_from_slice(&[0xff; 32]),
                        6 => signature = [0u8; 64],
                        7 => {
                            let b = (rng.next_u64() % 64) as usize;
                            signature[b] ^= 1 << (rng.next_u64() % 8);
                        }
                        _ => {}
                    }
                    cases.push(Case {
                        public_key,
                        signature,
                        message,
                    });
                }

                let inputs: Vec<VerifyInput<'_>> = cases.iter().map(|c| c.input()).collect();
                let solana_ed25519: Vec<bool> = inputs
                    .iter()
                    .map(|i| match policy {
                        Zip215 => solana_ed25519_verify_zebra(i.public_key, i.signature, i.message),
                        Dalek => solana_ed25519_verify_dalek(i.public_key, i.signature, i.message),
                    })
                    .collect();

                let mut verifier = Verifier::with_policy(policy);
                let mut out = vec![false; inputs.len()];
                verifier.verify_batch(&inputs, &mut out);
                for idx in 0..inputs.len() {
                    assert_eq!(
                        out[idx], solana_ed25519[idx],
                        "lru lane {idx} (policy={policy:?}, size={size}, trial={trial}) disagrees"
                    );
                }

                let mut cold = Verifier::with_cache(policy, NullKeyCache::new());
                let mut out_cold = vec![false; inputs.len()];
                cold.verify_batch(&inputs, &mut out_cold);
                for idx in 0..inputs.len() {
                    assert_eq!(
                        out_cold[idx], solana_ed25519[idx],
                        "null lane {idx} (policy={policy:?}, size={size}, trial={trial}) disagrees"
                    );
                }
            }
        }
    }
}

#[test]
fn enumerate_divergences_vs_solana_ed25519() {
    use ed25519_simd::VerifyPolicy::{Dalek, Zip215};

    let points: [(&str, [u8; 32]); 14] = [
        (
            "id_canon",
            hx("0100000000000000000000000000000000000000000000000000000000000000"),
        ),
        (
            "id_noncanon",
            hx("eeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"),
        ),
        (
            "y0_canon",
            hx("0000000000000000000000000000000000000000000000000000000000000000"),
        ),
        (
            "y0_sign",
            hx("0000000000000000000000000000000000000000000000000000000000000080"),
        ),
        (
            "y0_noncanon",
            hx("edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"),
        ),
        (
            "ord2",
            hx("ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"),
        ),
        (
            "ord8a",
            hx("26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc05"),
        ),
        (
            "ord8b",
            hx("26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc85"),
        ),
        (
            "ord8c",
            hx("c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a"),
        ),
        (
            "ord8d",
            hx("c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac03fa"),
        ),
        (
            "ord2_noncanon_hi",
            hx("ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"),
        ),
        ("valid", {
            let k = signing_key_from_index(7);
            <[u8; 32]>::from(VerificationKeyBytes::from(&k))
        }),
        (
            "garbage",
            hx("0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"),
        ),
        (
            "highbit_garbage",
            hx("0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1fff"),
        ),
    ];

    let l = hx("edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010");
    let mut l_minus_1 = l;
    l_minus_1[0] -= 1;
    let zero = [0u8; 32];
    let mut one = [0u8; 32];
    one[0] = 1;
    let scalars: [(&str, [u8; 32]); 5] = [
        ("s0", zero),
        ("s1", one),
        ("s_L-1", l_minus_1),
        ("s_L", l),
        ("s_FF", [0xff; 32]),
    ];
    let message: &[u8] = b"taming the many eddsas";

    let mut zebra_div = Vec::new();
    let mut dalek_div = Vec::new();
    let mut total = 0;

    for (a_name, a) in &points {
        for (r_name, r) in &points {
            for (s_name, s) in &scalars {
                let mut sig = [0u8; 64];
                sig[..32].copy_from_slice(r);
                sig[32..].copy_from_slice(s);
                total += 1;

                let ours_cof = ours_policy(*a, sig, message, Zip215);
                let solana_ed25519_zebra = solana_ed25519_verify_zebra(*a, sig, message);
                if ours_cof != solana_ed25519_zebra {
                    zebra_div.push((a_name, r_name, s_name, ours_cof, solana_ed25519_zebra));
                }

                let ours_strict = ours_policy(*a, sig, message, Dalek);
                let solana_ed25519_dalek = solana_ed25519_verify_dalek(*a, sig, message);
                if ours_strict != solana_ed25519_dalek {
                    dalek_div.push((a_name, r_name, s_name, ours_strict, solana_ed25519_dalek));
                }
            }
        }
    }

    eprintln!("\n=== {total} crafted cases ===");
    eprintln!(
        "cofactored vs solana-ed25519 verify_zebra (ZIP-215): {} divergences",
        zebra_div.len()
    );
    for (a, r, s, ours, solana_ed25519) in zebra_div.iter().take(20) {
        eprintln!("  A={a:18} R={r:18} {s:6} ours={ours} solana-ed25519={solana_ed25519}");
    }
    eprintln!(
        "strict vs solana-ed25519 verify_dalek: {} divergences",
        dalek_div.len()
    );
    for (a, r, s, ours, solana_ed25519) in dalek_div.iter().take(20) {
        eprintln!("  A={a:18} R={r:18} {s:6} ours={ours} solana-ed25519={solana_ed25519}");
    }
    eprintln!(
        "\nSUMMARY: zebra_divergences={} dalek_divergences={}",
        zebra_div.len(),
        dalek_div.len()
    );

    assert_eq!(
        zebra_div.len(),
        0,
        "cofactored policy must match solana-ed25519 verify_zebra"
    );
    assert_eq!(
        dalek_div.len(),
        0,
        "strict policy must match solana-ed25519 verify_dalek"
    );
}

#[test]
fn noncanonical_encoding_now_matches_solana_ed25519() {
    let mut public_key = [0xffu8; 32];
    public_key[0] = 0xee;
    public_key[31] = 0x7f;

    let mut signature = [0u8; 64];
    signature[0] = 1;

    let message = b"";

    let ours = ours_single(VerifyInput {
        public_key,
        signature,
        message,
    });
    let theirs = solana_ed25519_verify_zebra(public_key, signature, message);

    assert!(
        theirs,
        "solana-ed25519 ZIP-215 should accept the non-canonical encoding"
    );
    assert_eq!(
        ours, theirs,
        "crate must match solana-ed25519 on non-canonical encoding"
    );
}
