mod support;

use curve25519::ed_sigs::VerificationKeyBytes;
use ed25519_simd::{NullKeyCache, Verifier, VerifyInput, VerifyPolicy};
use support::{
    Case, signing_key_from_index, solana_ed25519_verify_dalek, solana_ed25519_verify_zebra,
    verify_batch,
};

#[test]
fn long_message_bucket_fallback_matches_solana_ed25519() {
    let lengths = [
        1usize, 8111, 128, 8112, 4096, 8113, 8191, 8192, 8193, 9000, 16384, 127, 65, 12288, 2048,
        10000, 63, 20000, 112, 24576, 113, 32768, 1024, 12000,
    ];
    let mut cases = Vec::with_capacity(lengths.len());

    for (idx, len) in lengths.into_iter().enumerate() {
        let mut message = vec![0u8; len];
        fill_message(&mut message, idx as u64);
        let signing_key = signing_key_from_index(0xb0c0_0000 + idx as u64);
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
                VerifyPolicy::Zip215 => {
                    solana_ed25519_verify_zebra(input.public_key, input.signature, input.message)
                }
                VerifyPolicy::Dalek => {
                    solana_ed25519_verify_dalek(input.public_key, input.signature, input.message)
                }
            })
            .collect();

        assert_eq!(
            verify_batch(policy, &inputs),
            expected,
            "null-cache {policy:?}"
        );

        let mut verifier = Verifier::with_policy(policy);
        let mut out = vec![false; inputs.len()];
        verifier.verify_batch(&inputs, &mut out);
        assert_eq!(out, expected, "lru-cache {policy:?}");
    }
}

#[test]
fn every_small_batch_tail_lane_can_fail_independently() {
    for policy in [VerifyPolicy::Zip215, VerifyPolicy::Dalek] {
        let mut verifier = Verifier::with_cache(policy, NullKeyCache::new());
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
                let mut verifier = Verifier::with_cache(policy, NullKeyCache::new());

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
    let mut state = seed ^ 0x9e37_79b9_7f4a_7c15;
    for byte in message {
        state = state
            .wrapping_mul(0xd134_2543_de82_ef95)
            .wrapping_add(0xa076_1d64_78bd_642f);
        *byte = (state >> 56) as u8;
    }
}
