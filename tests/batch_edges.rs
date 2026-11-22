mod support;

use curve25519::ed_sigs::VerificationKeyBytes;
use ed25519_simd::{RuntimeVerifier, VerifyInput, VerifyPolicy};
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
                "{name}, {policy:?}"
            );
        }
    }
}

#[test]
fn each_lane_failure_is_isolated_across_small_batches() {
    for policy in [VerifyPolicy::Zip215, VerifyPolicy::Dalek] {
        let mut verifier = RuntimeVerifier::with_policy(policy);
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
fn reused_verifier_rechecks_keys_and_scalars_in_every_lane() {
    let cases = valid_cases(8);
    let inputs: Vec<_> = cases.iter().map(Case::input).collect();
    let mut rejected = inputs.clone();
    for (lane, input) in rejected.iter_mut().enumerate() {
        if lane % 2 == 0 {
            // y = 2 has no Edwards x.
            input.public_key = [0; 32];
            input.public_key[0] = 2;
        } else {
            input.signature[32..].fill(0xff);
        }
    }

    for policy in [VerifyPolicy::Zip215, VerifyPolicy::Dalek] {
        let mut verifier = RuntimeVerifier::with_policy(policy);
        let mut out = [false; 8];
        verifier.verify_batch(&inputs, &mut out);
        assert_eq!(out, [true; 8]);
        verifier.verify_batch(&rejected, &mut out);
        assert_eq!(out, [false; 8]);
        verifier.verify_batch(&inputs, &mut out);
        assert_eq!(out, [true; 8]);
    }
}

#[test]
fn zip215_scatter_across_sorted_chunks_and_a_tail() {
    use ed25519_simd::Zip215Verifier;

    // Give each group of eight a distinct SHA-512 block count.
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
    let mut out: Vec<_> = expected.iter().map(|v| !v).collect();
    Zip215Verifier::new().verify_batch(&inputs, &mut out);
    assert_eq!(out, expected);
}

#[test]
fn zip215_preserves_cofactored_acceptance() {
    use ed25519_simd::Zip215Verifier;

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

    let mut verifier = Zip215Verifier::new();
    let inputs: Vec<_> = cases.iter().map(Case::input).collect();
    let expected: Vec<_> = inputs
        .iter()
        .map(|v| solana_ed25519_verify_zebra(v.public_key, v.signature, v.message))
        .collect();
    for n in [8, 16, 24, 32, 56, 63, 64, 67] {
        let mut out: Vec<_> = expected[..n].iter().map(|v| !v).collect();
        verifier.verify_batch(&inputs[..n], &mut out);
        assert_eq!(out, expected[..n], "batch of {n}");
    }
}

#[test]
fn dalek_reused_verifier_matches_strict_verification() {
    use ed25519_simd::DalekVerifier;

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
    let mut verifier = DalekVerifier::new();
    let inputs: Vec<_> = cases.iter().map(Case::input).collect();
    let expected: Vec<_> = inputs
        .iter()
        .map(|v| solana_ed25519_verify_dalek(v.public_key, v.signature, v.message))
        .collect();

    for n in [73, 0, 1, 15, 24, 31, 40, 47, 56, 63, 64, 65, 73] {
        let mut out: Vec<_> = expected[..n].iter().map(|ok| !ok).collect();
        verifier.verify_batch(&inputs[..n], &mut out);
        assert_eq!(out, expected[..n], "count {n}");
    }
}

#[test]
fn dalek_rejected_chunks_and_padded_tails_match_strict_verification() {
    use ed25519_simd::DalekVerifier;

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
    let mut verifier = DalekVerifier::new();
    for n in [1, 7, 8, 11, 16, 19, 24, 25, 31, 32] {
        let mut out: Vec<_> = expected[..n].iter().map(|ok| !ok).collect();
        verifier.verify_batch(&inputs[..n], &mut out);
        assert_eq!(out, expected[..n], "decoded batch of {n}");
    }
}
