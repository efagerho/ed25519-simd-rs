mod support;

use core::convert::TryInto;

use curve25519::ed_sigs::VerificationKeyBytes;
use ed25519_simd::{VerifyInput, VerifyPolicy};
use serde_json::Value;
use support::{
    Case, hex_array, hex_vec, signing_key_from_index, solana_ed25519_verify_dalek,
    solana_ed25519_verify_zebra, verify,
};

const L_BYTES: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
];

#[test]
fn wycheproof_fixed_length_vectors_match_dalek_policy() {
    let suite: Value =
        serde_json::from_str(include_str!("vectors/ed25519_wycheproof.json")).unwrap();
    let mut checked = 0usize;
    let mut skipped_wrong_length = 0usize;

    for group in suite["testGroups"].as_array().unwrap() {
        let public_key = array_from_hex::<32>(group["publicKey"]["pk"].as_str().unwrap());
        for test in group["tests"].as_array().unwrap() {
            let sig = hex_vec(test["sig"].as_str().unwrap());
            if sig.len() != 64 {
                skipped_wrong_length += 1;
                continue;
            }

            let message = hex_vec(test["msg"].as_str().unwrap());
            let signature = sig.try_into().unwrap();
            let input = VerifyInput {
                public_key,
                signature,
                message: &message,
            };
            let expected = match test["result"].as_str().unwrap() {
                "valid" => true,
                "invalid" => false,
                other => panic!("unexpected Wycheproof result {other}"),
            };

            assert_eq!(
                verify(VerifyPolicy::Dalek, input),
                expected,
                "Wycheproof tcId={} flags={:?}",
                test["tcId"],
                test["flags"]
            );
            // Wycheproof expectations are Dalek-oriented; pin ZIP-215 against
            // the solana-ed25519 oracle instead.
            let zip215_oracle = solana_ed25519_verify_zebra(public_key, signature, &message);
            assert_eq!(
                verify(VerifyPolicy::Zip215, input),
                zip215_oracle,
                "Wycheproof tcId={} ZIP-215 disagrees with solana-ed25519 oracle",
                test["tcId"]
            );
            checked += 1;
        }
    }

    assert_eq!(checked, 138);
    assert_eq!(skipped_wrong_length, 12);
}

#[test]
fn speccheck_vectors_match_zip215_and_dalek_policies() {
    let cases: Value =
        serde_json::from_str(include_str!("vectors/ed25519_speccheck.json")).unwrap();
    let cases = cases.as_array().unwrap();

    // Pinned speccheck expectations: Dalek rejects the small-/mixed-order cases
    // accepted by ZIP-215; both reject non-canonical S. solana-ed25519 is
    // cross-checked against these arrays as a fixture guard.
    let zip215_expected = [
        true, true, true, true, true, true, false, false, false, true, true, true,
    ];
    let dalek_expected = [
        false, true, true, true, false, false, false, false, false, false, false, true,
    ];

    assert_eq!(cases.len(), 12);
    for (idx, case) in cases.iter().enumerate() {
        let public_key = array_from_hex::<32>(case["pub_key"].as_str().unwrap());
        let signature = array_from_hex::<64>(case["signature"].as_str().unwrap());
        let message = hex_vec(case["message"].as_str().unwrap());
        let input = VerifyInput {
            public_key,
            signature,
            message: &message,
        };

        assert_eq!(
            verify(VerifyPolicy::Zip215, input),
            zip215_expected[idx],
            "speccheck vector {idx} ZIP-215 mismatch"
        );
        assert_eq!(
            solana_ed25519_verify_zebra(public_key, signature, &message),
            zip215_expected[idx],
            "speccheck vector {idx} solana-ed25519 ZIP-215 fixture expectation mismatch"
        );
        assert_eq!(
            verify(VerifyPolicy::Dalek, input),
            dalek_expected[idx],
            "speccheck vector {idx} Dalek mismatch"
        );
        assert_eq!(
            solana_ed25519_verify_dalek(public_key, signature, &message),
            dalek_expected[idx],
            "speccheck vector {idx} solana-ed25519 Dalek fixture expectation mismatch"
        );
    }
}

#[test]
fn signatures_malleated_by_adding_group_order_are_rejected() {
    let mut cases = Vec::new();
    for (case_idx, len) in [0usize, 1, 64, 255, 1024].into_iter().enumerate() {
        let mut message = vec![0u8; len];
        for (i, byte) in message.iter_mut().enumerate() {
            *byte = (case_idx as u8).wrapping_mul(31).wrapping_add(i as u8);
        }
        let signing_key = signing_key_from_index(0x5a17_0000 + case_idx as u64);
        let public_key = <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key));
        let signature = signing_key.sign(&message).to_bytes();
        cases.push(Case {
            public_key,
            signature,
            message,
        });
    }

    for (idx, case) in cases.iter().enumerate() {
        for policy in [VerifyPolicy::Zip215, VerifyPolicy::Dalek] {
            assert!(
                verify(policy, case.input()),
                "{policy:?} rejected valid case {idx}"
            );
        }

        let mut malleated = case.signature;
        add_group_order_to_s(&mut malleated);
        let input = VerifyInput {
            public_key: case.public_key,
            signature: malleated,
            message: &case.message,
        };

        for policy in [VerifyPolicy::Zip215, VerifyPolicy::Dalek] {
            assert!(
                !verify(policy, input),
                "{policy:?} accepted S+L malleated signature {idx}"
            );
        }
    }
}

fn add_group_order_to_s(signature: &mut [u8; 64]) {
    let mut carry = 0u16;
    for (byte, addend) in signature[32..].iter_mut().zip(L_BYTES) {
        let sum = *byte as u16 + addend as u16 + carry;
        *byte = sum as u8;
        carry = sum >> 8;
    }
    assert_eq!(carry, 0);
}

fn array_from_hex<const N: usize>(hex: &str) -> [u8; N] {
    hex_array(hex)
}
