//! Acceptance tests against solana-ed25519's ZIP-215 and Dalek verifiers.

mod support;

use curve25519::ed_sigs::VerificationKeyBytes;
use ed25519_simd::{
    DalekVerifier, HotKeyCache, KeyCache, NullKeyCache, PUBLIC_KEY_LEN, RuntimeVerifier,
    SIGNATURE_LEN, VerifyInput, VerifyPolicy, Zip215Verifier,
};
use rand::{RngCore, SeedableRng, rngs::StdRng};
use support::{
    Case, hex_array, signing_key_from_index, solana_ed25519_verify_dalek,
    solana_ed25519_verify_zebra, verify, verify_warm,
};

/// Stresses the SIMD distinct-key decode/table path against solana-ed25519.
#[test]
fn null_cache_decode_build_stress() {
    let mut rng = StdRng::seed_from_u64(0x5151_5151_5151_5151);
    let mut zip = Zip215Verifier::with_cache(NullKeyCache::new());
    let mut dalek = DalekVerifier::with_cache(NullKeyCache::new());

    for _ in 0..400 {
        let len = (rng.next_u64() % 257) as usize;
        let mut cases: Vec<Case> = Vec::with_capacity(8);
        for _ in 0..8 {
            let mut message = vec![0u8; len];
            rng.fill_bytes(&mut message);
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
fn cached_batches_match_solana_ed25519() {
    for policy in [VerifyPolicy::Zip215, VerifyPolicy::Dalek] {
        for &size in &[8usize, 9, 16, 24, 31, 32] {
            for trial in 0..6u64 {
                let mut rng = StdRng::seed_from_u64(
                    0xba7c_0000 + policy as u64 * 0x100_0000 + trial * 911 + size as u64,
                );
                let uniform_key = trial % 2 == 0;
                let len = (rng.next_u64() % 200) as usize;
                let shared_key = rng.next_u64();

                let mut cases = Vec::with_capacity(size);
                for lane in 0..size {
                    let mut message = vec![0u8; len];
                    rng.fill_bytes(&mut message);
                    let key_index = if uniform_key {
                        shared_key
                    } else {
                        rng.next_u64()
                    };
                    let signing_key = signing_key_from_index(key_index);
                    let public_key = <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key));
                    let mut signature = signing_key.sign(&message).to_bytes();
                    match rng.next_u64() % 8 {
                        0 => {
                            let byte = (rng.next_u64() % 64) as usize;
                            signature[byte] ^= 1 << (rng.next_u64() % 8);
                        }
                        1 if policy == VerifyPolicy::Dalek => {
                            signature[..32].copy_from_slice(&[0u8; 32]);
                        }
                        2 if policy == VerifyPolicy::Dalek && lane == 0 => {
                            signature[..32].fill(0);
                            signature[0] = 1;
                        }
                        _ => {}
                    }
                    cases.push(Case {
                        public_key,
                        signature,
                        message,
                    });
                }

                let inputs: Vec<VerifyInput<'_>> = cases.iter().map(Case::input).collect();
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

                let mut verifier =
                    RuntimeVerifier::with_cache(policy, HotKeyCache::with_capacity(1024));
                for path in ["cold", "warm"] {
                    let mut out = vec![false; inputs.len()];
                    verifier.verify_batch(&inputs, &mut out);
                    assert_eq!(
                        out, expected,
                        "{path} {policy:?}, size={size}, uniform_key={uniform_key}"
                    );
                }
            }
        }
    }
}

#[test]
fn hot_key_capacity_does_not_evict_current_simd_chunk() {
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
    let mut verifier = Zip215Verifier::with_cache(HotKeyCache::with_capacity(1));
    let mut out = vec![false; inputs.len()];
    verifier.verify_batch(&inputs, &mut out);

    assert_eq!(out, vec![true; 8]);
    let resident = cases
        .iter()
        .filter(|case| verifier.cache().get(&case.public_key).is_some())
        .count();
    assert_eq!(resident, 1);
}

/// Exercises per-lane validity masking across keys, `R`, and `s`.
#[test]
fn per_lane_masking_matches_solana_ed25519_under_heavy_garbage() {
    use ed25519_simd::VerifyPolicy::{Dalek, Zip215};

    for &policy in &[Zip215, Dalek] {
        for &size in &[1usize, 8, 9, 16, 17, 32, 33, 64] {
            for trial in 0..8u64 {
                let mut rng = StdRng::seed_from_u64(
                    0x6a11_0000 + trial * 1009 + size as u64 * 7 + policy as u64,
                );
                let len = (rng.next_u64() % 96) as usize;

                let mut cases: Vec<Case> = Vec::with_capacity(size);
                for _ in 0..size {
                    let mut message = vec![0u8; len];
                    rng.fill_bytes(&mut message);
                    let signing_key = signing_key_from_index(rng.next_u64());
                    let mut public_key = <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key));
                    let mut signature = signing_key.sign(&message).to_bytes();

                    match rng.next_u64() % 10 {
                        0 => rng.fill_bytes(&mut public_key),
                        1 => public_key = [0u8; 32],
                        2 => rng.fill_bytes(&mut signature[..32]),
                        3 => signature[..32].copy_from_slice(&[0xff; 32]),
                        4 => rng.fill_bytes(&mut signature[32..]),
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

                let mut verifier =
                    RuntimeVerifier::with_cache(policy, HotKeyCache::with_capacity(1024));
                let mut out = vec![false; inputs.len()];
                verifier.verify_batch(&inputs, &mut out);
                for idx in 0..inputs.len() {
                    assert_eq!(
                        out[idx], solana_ed25519[idx],
                        "hot-key cache lane {idx} (policy={policy:?}, size={size}, trial={trial}) disagrees"
                    );
                }

                let mut cold = RuntimeVerifier::with_cache(policy, NullKeyCache::new());
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
fn edge_case_grid_matches_solana_ed25519() {
    use ed25519_simd::VerifyPolicy::{Dalek, Zip215};

    let points: [(&str, [u8; 32]); 18] = [
        (
            "id_canon",
            hex_array::<32>("0100000000000000000000000000000000000000000000000000000000000000"),
        ),
        (
            "id_noncanon",
            hex_array::<32>("eeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"),
        ),
        (
            "y0_canon",
            hex_array::<32>("0000000000000000000000000000000000000000000000000000000000000000"),
        ),
        (
            "y0_sign",
            hex_array::<32>("0000000000000000000000000000000000000000000000000000000000000080"),
        ),
        (
            "y0_noncanon",
            hex_array::<32>("edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"),
        ),
        (
            "ord2",
            hex_array::<32>("ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"),
        ),
        (
            "ord8a",
            hex_array::<32>("26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc05"),
        ),
        (
            "ord8b",
            hex_array::<32>("26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc85"),
        ),
        (
            "ord8c",
            hex_array::<32>("c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a"),
        ),
        (
            "ord8d",
            hex_array::<32>("c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac03fa"),
        ),
        // Historical solana-ed25519 0.1.x blacklist entries, retained to catch
        // acceptance changes in valid non-small-order and malformed points.
        (
            "legacy_excl_valid_pt1",
            hex_array::<32>("13e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc85"),
        ),
        (
            "legacy_excl_invalid_pt",
            hex_array::<32>("b4176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac03fa"),
        ),
        (
            "legacy_excl_offcurve",
            hex_array::<32>("d9ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"),
        ),
        (
            "legacy_excl_valid_pt2",
            hex_array::<32>("daffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"),
        ),
        (
            "ord2_noncanon_hi",
            hex_array::<32>("ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"),
        ),
        ("valid", {
            let k = signing_key_from_index(7);
            <[u8; 32]>::from(VerificationKeyBytes::from(&k))
        }),
        (
            "garbage",
            hex_array::<32>("0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"),
        ),
        (
            "highbit_garbage",
            hex_array::<32>("0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1fff"),
        ),
    ];

    let l = hex_array::<32>("edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010");
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

    /// Signature of a reference verifier used as a policy oracle.
    type Oracle = fn([u8; PUBLIC_KEY_LEN], [u8; SIGNATURE_LEN], &[u8]) -> bool;
    let policies: [(VerifyPolicy, Oracle); 2] = [
        (Zip215, solana_ed25519_verify_zebra),
        (Dalek, solana_ed25519_verify_dalek),
    ];

    for (a_name, a) in &points {
        for (r_name, r) in &points {
            for (s_name, s) in &scalars {
                let mut sig = [0u8; 64];
                sig[..32].copy_from_slice(r);
                sig[32..].copy_from_slice(s);

                let input = VerifyInput {
                    public_key: *a,
                    signature: sig,
                    message,
                };

                for (policy, oracle) in policies {
                    let expected = oracle(*a, sig, message);
                    for (path, actual) in [
                        ("cold", verify(policy, input)),
                        ("warm", verify_warm(policy, input)),
                    ] {
                        assert_eq!(
                            actual, expected,
                            "A={a_name}, R={r_name}, S={s_name}, {policy:?} {path}"
                        );
                    }
                }
            }
        }
    }
}
