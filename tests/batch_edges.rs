mod support;

use curve25519::ed_sigs::VerificationKeyBytes;
use ed25519_simd::{HotKeyCache, NullKeyCache, RuntimeVerifier, VerifyInput, VerifyPolicy};
use rand::{RngCore, SeedableRng, rngs::StdRng};
use support::{
    Case, signing_key_from_index, solana_ed25519_verify_dalek, solana_ed25519_verify_zebra,
    verify_batch,
};

#[test]
fn block_sorted_batch_shapes_match_solana_ed25519() {
    let regular = [
        1usize, 2048, 64, 1024, 2, 1536, 128, 4096, 3, 512, 65, 2047, 4, 256, 112, 3072, 5, 1025,
        63, 2048, 6, 768, 127, 4095, 7, 1537, 48, 1024, 8, 511, 113, 2048, 9, 4096, 64, 1023, 10,
        256, 129, 3071,
    ];
    let tail = [
        1usize, 2048, 64, 1024, 2, 1536, 128, 4096, 3, 512, 65, 2047, 4, 256, 112, 3072, 5,
    ];
    let long = [
        1usize, 8111, 128, 8112, 4096, 8113, 8191, 8192, 8193, 9000, 16384, 127, 65, 12288, 2048,
        10000, 63, 20000, 112, 24576, 113, 32768, 1024, 12000,
    ];
    let profiles: [(&str, &[usize], u64); 3] = [
        ("regular", &regular, 0xb0cc_0000),
        ("17-element tail", &tail, 0xba7c_0000),
        ("long messages", &long, 0xb0c0_0000),
    ];

    for (name, lengths, seed) in profiles {
        let mut cases = Vec::with_capacity(lengths.len());
        for (idx, &len) in lengths.iter().enumerate() {
            let mut message = vec![0u8; len];
            fill_message(&mut message, seed + idx as u64);
            let signing_key = signing_key_from_index(seed + 0x10000 + idx as u64);
            let public_key = <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key));
            let mut signature = signing_key.sign(&message).to_bytes();
            if idx % 6 == 4 {
                signature[(idx * 7) % 64] ^= 0x20;
            }
            cases.push(Case {
                public_key,
                signature,
                message,
            });
        }

        let inputs: Vec<VerifyInput<'_>> = cases.iter().map(Case::input).collect();
        for policy in [VerifyPolicy::Zip215, VerifyPolicy::Dalek] {
            let expected: Vec<bool> = inputs
                .iter()
                .map(|input| match policy {
                    VerifyPolicy::Zip215 => solana_ed25519_verify_zebra(
                        input.public_key,
                        input.signature,
                        input.message,
                    ),
                    VerifyPolicy::Dalek => solana_ed25519_verify_dalek(
                        input.public_key,
                        input.signature,
                        input.message,
                    ),
                })
                .collect();

            assert_eq!(
                verify_batch(policy, &inputs),
                expected,
                "{name}, null-cache {policy:?}"
            );

            let mut verifier =
                RuntimeVerifier::with_cache(policy, HotKeyCache::with_capacity(1024));
            let mut out = vec![false; inputs.len()];
            verifier.verify_batch(&inputs, &mut out);
            assert_eq!(out, expected, "{name}, hot-key cache {policy:?}");
        }
    }
}

#[test]
fn each_lane_failure_is_isolated_across_small_batches() {
    for policy in [VerifyPolicy::Zip215, VerifyPolicy::Dalek] {
        let mut verifier = RuntimeVerifier::with_cache(policy, NullKeyCache::new());
        let empty: [VerifyInput<'_>; 0] = [];
        let mut empty_out: [bool; 0] = [];
        verifier.verify_batch(&empty, &mut empty_out);

        for size in 1..=32 {
            let base = valid_cases(size);
            for bad_lane in 0..size {
                let mut cases = base.clone();
                cases[bad_lane].signature[40] ^= 1;
                let inputs: Vec<VerifyInput<'_>> = cases.iter().map(Case::input).collect();
                let mut out = vec![false; size];
                let mut verifier = RuntimeVerifier::with_cache(policy, NullKeyCache::new());

                verifier.verify_batch(&inputs, &mut out);

                for (lane, &accepted) in out.iter().enumerate() {
                    assert_eq!(
                        accepted,
                        lane != bad_lane,
                        "{policy:?} size={size} bad_lane={bad_lane} lane={lane}"
                    );
                }
            }
        }
    }
}

fn valid_cases(size: usize) -> Vec<Case> {
    let mut cases = Vec::with_capacity(size);
    for lane in 0..size {
        let mut message = vec![0u8; 33];
        fill_message(&mut message, (size * 257 + lane) as u64);
        let signing_key = signing_key_from_index(0x7a11_0000 + size as u64 * 64 + lane as u64);
        let public_key = <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key));
        let signature = signing_key.sign(&message).to_bytes();
        cases.push(Case {
            public_key,
            signature,
            message,
        });
    }
    cases
}

fn fill_message(message: &mut [u8], seed: u64) {
    StdRng::seed_from_u64(seed ^ 0x9e37_79b9_7f4a_7c15).fill_bytes(message);
}

#[test]
fn zip215_scatter_across_deferred_pairs_misses_and_a_tail() {
    use ed25519_simd::{CachedPublicKey, KeyCache, Zip215Verifier};

    // Each group of eight is a distinct SHA block count. Queue the first,
    // score the mixed-hit second immediately, pair the third with the first,
    // and flush the three-lane tail on its own.
    let mut cache = HotKeyCache::with_capacity(32);
    let mut cases = Vec::new();
    for i in 0..27 {
        let key = signing_key_from_index(0x2150 + i as u64);
        let message = vec![i as u8; 1 + 128 * (i / 8)];
        let mut public_key = <[u8; 32]>::from(VerificationKeyBytes::from(&key));
        let mut signature = key.sign(&message).to_bytes();
        if matches!(i, 1 | 2 | 9 | 11 | 17 | 19 | 24 | 25) {
            // ZIP-215 accepts both signs of x=0 and y=p+1 for the identity.
            // With A=identity the equation still holds if an invalid S below
            // is replaced by zero digits. Only the input-valid mask rejects it.
            public_key = [0; 32];
            public_key[0] = 1;
            signature = [0; 64];
            signature[..32].fill(0xff);
            signature[0] = 0xee;
        }
        if i != 10 {
            cache.insert(CachedPublicKey::from_encoded(public_key).unwrap());
        }
        match i {
            2 | 11 | 19 | 25 => signature[32..].fill(0xff), // S >= L
            6 | 12 | 16 => signature[32] ^= 1,              // wrong equation
            5 | 14 | 20 => {
                // y = 2 has no Edwards x
                signature[..32].fill(0);
                signature[0] = 2;
            }
            _ => {}
        }
        cases.push(Case {
            public_key,
            signature,
            message,
        });
    }
    // Interleave the groups in caller order so scatter indices are nonconsecutive.
    let inputs: Vec<_> = (0..27).map(|i| cases[(i * 8) % 27].input()).collect();
    let expected: Vec<_> = inputs
        .iter()
        .map(|v| solana_ed25519_verify_zebra(v.public_key, v.signature, v.message))
        .collect();
    let mut hot = Zip215Verifier::with_cache(cache);
    let mut cold = Zip215Verifier::new();
    for path in ["mixed", "all hit", "uncached"] {
        let mut out: Vec<_> = expected.iter().map(|v| !v).collect();
        if path == "uncached" {
            cold.verify_batch(&inputs, &mut out);
        } else {
            hot.verify_batch(&inputs, &mut out);
        }
        assert_eq!(out, expected, "{path}");
    }
}

#[test]
fn zip215_recompression_preserves_cofactored_acceptance() {
    use ed25519_simd::{CachedPublicKey, KeyCache, Zip215Verifier};

    let mut cases = valid_cases(67);
    let mut identity = [0; 32];
    identity[0] = 1;
    let mut base = [0x66; 32];
    base[0] = 0x58;
    let mut negative_base = base;
    negative_base[31] |= 0x80;
    // With A = identity the candidate is [S]B regardless of the digest.
    // B and -B have the same encoded y, but only the positive sign satisfies
    // the equation for S=1. For S=0 the order-four point y=0 is ZIP-215 valid.
    for (i, r, s, accepts) in [
        (8, negative_base, 1, false),
        (16, [0; 32], 0, true),
        (39, base, 1, true),
        (48, negative_base, 1, false),
        (62, [0; 32], 0, true),
        (63, negative_base, 1, false),
        (66, negative_base, 1, false),
    ] {
        let case = &mut cases[i];
        case.public_key = identity;
        case.signature = [0; 64];
        case.signature[..32].copy_from_slice(&r);
        case.signature[32] = s;
        assert_eq!(
            solana_ed25519_verify_zebra(identity, case.signature, &case.message),
            accepts
        );
    }

    let mut cache = HotKeyCache::with_capacity(cases.len());
    for case in &cases {
        cache.insert(CachedPublicKey::from_encoded(case.public_key).unwrap());
    }
    let mut verifier = Zip215Verifier::with_cache(cache);
    let inputs: Vec<_> = cases.iter().map(Case::input).collect();
    let expected: Vec<_> = inputs
        .iter()
        .map(|v| solana_ed25519_verify_zebra(v.public_key, v.signature, v.message))
        .collect();
    for n in [8, 16, 24, 32, 56, 63, 64, 67] {
        let mut out: Vec<_> = expected[..n].iter().map(|v| !v).collect();
        verifier.verify_batch(&inputs[..n], &mut out);
        assert_eq!(out, expected[..n], "warm batch of {n}");
    }
}

#[test]
fn dalek_deferred_queue_and_mixed_hits_match_strict_verification() {
    use ed25519_simd::{CachedPublicKey, DalekVerifier, KeyCache};

    let mut cases = valid_cases(73);
    for (i, case) in cases.iter_mut().enumerate() {
        match i % 11 {
            1 => case.signature[31] ^= 0x80, // opposite X, same Y
            3 => case.signature[32..].fill(0xff),
            5 => {
                case.signature[..32].fill(0xff); // noncanonical y=p+1
                case.signature[0] = 0xee;
            }
            7 => {
                case.signature[..32].fill(0); // negative zero at y=1
                case.signature[0] = 1;
                case.signature[31] = 0x80;
            }
            9 => case.signature[40] ^= 1,
            _ => {}
        }
    }
    let mut cache = HotKeyCache::with_capacity(cases.len());
    for (i, case) in cases.iter().enumerate() {
        if i != 18 {
            cache.insert(CachedPublicKey::from_encoded(case.public_key).unwrap());
        }
    }
    let mut hot = DalekVerifier::with_cache(cache);
    let mut cold = DalekVerifier::new();
    let inputs: Vec<_> = cases.iter().map(Case::input).collect();
    let expected: Vec<_> = inputs
        .iter()
        .map(|v| solana_ed25519_verify_dalek(v.public_key, v.signature, v.message))
        .collect();

    // First interleave a decoded chunk with queued hits. Subsequent calls
    // exercise queue reuse, all eight occupancies, automatic flush and a tail.
    for n in [73, 0, 1, 15, 24, 31, 40, 47, 56, 63, 64, 65, 73] {
        let mut out: Vec<_> = expected[..n].iter().map(|ok| !ok).collect();
        hot.verify_batch(&inputs[..n], &mut out);
        assert_eq!(out, expected[..n], "cached, count {n}");
        for result in &mut out {
            *result = !*result;
        }
        cold.verify_batch(&inputs[..n], &mut out);
        assert_eq!(out, expected[..n], "uncached, count {n}");
    }
}

#[test]
fn dalek_rejected_chunks_and_padded_tails_match_strict_verification() {
    use ed25519_simd::{CachedPublicKey, DalekVerifier, KeyCache};

    let mut cases = valid_cases(32);
    for (i, case) in cases.iter_mut().enumerate() {
        let (r, s) = case.signature.split_at_mut(32);
        match i / 8 {
            // The eligible S mask and decodable R mask are disjoint.
            0 if i % 2 == 0 => s.fill(0xff),
            0 => {
                r.fill(0);
                r[0] = 2; // No Edwards point with this Y.
            }
            1 => {
                r.fill(0xff);
                r[0] = 0xee; // y = p+1, both signs
                r[31] = if i % 2 == 0 { 0x7f } else { 0xff };
            }
            2 => {
                r.fill(0);
                r[0] = 1; // Identity, including negative zero.
                r[31] = (i % 2) as u8 * 0x80;
            }
            _ if i != 31 => r.fill(0), // Order four, next to one valid lane.
            _ => {}
        }
    }
    let inputs: Vec<_> = cases.iter().map(Case::input).collect();
    let expected: Vec<_> = inputs
        .iter()
        .map(|v| solana_ed25519_verify_dalek(v.public_key, v.signature, v.message))
        .collect();
    assert_eq!(expected.iter().filter(|ok| **ok).count(), 1);
    assert!(expected[31]);
    let mut cache = HotKeyCache::with_capacity(cases.len());
    for case in &cases {
        cache.insert(CachedPublicKey::from_encoded(case.public_key).unwrap());
    }
    let mut hot = DalekVerifier::with_cache(cache);
    let mut cold = DalekVerifier::new();
    for n in [1, 7, 8, 11, 16, 19, 24, 25, 31, 32] {
        let mut out: Vec<_> = expected[..n].iter().map(|ok| !ok).collect();
        cold.verify_batch(&inputs[..n], &mut out);
        assert_eq!(out, expected[..n], "decoded batch of {n}");
        out.iter_mut().for_each(|ok| *ok = !*ok);
        hot.verify_batch(&inputs[..n], &mut out);
        assert_eq!(out, expected[..n], "cached batch of {n}");
    }
}
