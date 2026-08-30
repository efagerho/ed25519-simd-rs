mod support;

use curve25519::ed_sigs::VerificationKeyBytes;
use ed25519_simd::{HotKeyCache, NullKeyCache, RuntimeVerifier, VerifyInput, VerifyPolicy};
use rand::{RngCore, SeedableRng, rngs::StdRng};
use support::{
    Case, signing_key_from_index, solana_ed25519_verify_dalek, solana_ed25519_verify_zebra,
    verify_batch,
};

#[test]
fn bucketed_batch_shapes_match_solana_ed25519() {
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
