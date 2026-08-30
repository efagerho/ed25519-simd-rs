mod support;

use curve25519::ed_sigs::VerificationKeyBytes;
use ed25519_simd::{
    CachedPublicKey, DalekVerifier, HotKeyCache, KeyCache, NullKeyCache, PUBLIC_KEY_LEN,
    RuntimeVerifier, VerifyInput, VerifyPolicy, Zip215Verifier,
};
use support::{Case, hex_array, signing_key_from_index};

fn resident_count(cache: &HotKeyCache, keys: &[[u8; PUBLIC_KEY_LEN]]) -> usize {
    keys.iter().filter(|key| cache.get(key).is_some()).count()
}

fn off_curve_key() -> [u8; PUBLIC_KEY_LEN] {
    // y=p-20 with the sign bit set is not on the curve.
    hex_array("d9ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")
}

#[test]
fn verify_input_supports_struct_update_syntax_downstream() {
    let base = VerifyInput {
        public_key: [0; 32],
        signature: [0; 64],
        message: b"base",
    };
    let inputs: Vec<_> = [b"first".as_slice(), b"second".as_slice()]
        .into_iter()
        .map(|message| VerifyInput { message, ..base })
        .collect();

    assert_eq!(inputs[0].message, b"first");
    assert_eq!(inputs[1].message, b"second");
}

#[test]
fn hot_key_cache_handles_mixed_hit_and_miss_lanes_in_one_chunk() {
    let signing_keys: Vec<_> = (0..8u64).map(signing_key_from_index).collect();
    let public_keys: Vec<[u8; PUBLIC_KEY_LEN]> = signing_keys
        .iter()
        .map(|sk| <[u8; 32]>::from(VerificationKeyBytes::from(sk)))
        .collect();
    let message = b"mixed hit/miss chunk";
    let mut inputs: Vec<VerifyInput<'_>> = signing_keys
        .iter()
        .zip(public_keys.iter())
        .map(|(sk, pk)| VerifyInput {
            public_key: *pk,
            signature: sk.sign(message.as_slice()).to_bytes(),
            message: message.as_slice(),
        })
        .collect();

    let mut verifier = Zip215Verifier::with_cache(HotKeyCache::with_capacity(1024));
    let warm_inputs: Vec<VerifyInput<'_>> = inputs.iter().step_by(2).copied().collect();
    let mut warm_out = vec![false; warm_inputs.len()];
    verifier.verify_batch(&warm_inputs, &mut warm_out);
    assert!(warm_out.iter().all(|&valid| valid));
    let warm_public_keys: Vec<[u8; PUBLIC_KEY_LEN]> =
        public_keys.iter().step_by(2).copied().collect();
    assert_eq!(resident_count(verifier.cache(), &warm_public_keys), 4);

    // Corrupt S in one hit lane and make R invalid in one miss lane.
    inputs[2].signature[40] ^= 1;
    inputs[3].signature[..32].copy_from_slice(&[0xff; 32]);

    let mut out = [false; 8];
    verifier.verify_batch(&inputs, &mut out);
    assert_eq!(out, [true, true, false, false, true, true, true, true]);

    // The previously-missing keys are now cached too (all 8 resident).
    assert_eq!(resident_count(verifier.cache(), &public_keys), 8);
}

/// A chunk can end with no accepted lane only after the key decode has already
/// run: some lane must pass the `S` check to get that far. The tables that
/// decode produced are paid for, so they must still reach the cache.
#[test]
fn keys_decoded_in_an_all_rejected_chunk_are_still_retained() {
    let message = b"every lane rejected";
    // Lanes 0..4: real keys, but a non-canonical `S` rejects them.
    let signing_keys: Vec<_> = (0..4u64)
        .map(|i| signing_key_from_index(0x0a11_bad0 + i))
        .collect();
    let decodable_keys: Vec<[u8; PUBLIC_KEY_LEN]> = signing_keys
        .iter()
        .map(|sk| <[u8; 32]>::from(VerificationKeyBytes::from(sk)))
        .collect();
    let mut inputs: Vec<VerifyInput<'_>> = signing_keys
        .iter()
        .zip(decodable_keys.iter())
        .map(|(sk, pk)| {
            let mut signature = sk.sign(message.as_slice()).to_bytes();
            signature[32..].copy_from_slice(&[0xff; 32]);
            VerifyInput {
                public_key: *pk,
                signature,
                message: message.as_slice(),
            }
        })
        .collect();

    // Lanes 4..8: a canonical `S` so the chunk reaches the decode, paired with a
    // public key that does not decompress.
    let off_curve = off_curve_key();
    let good_s = signing_keys[0].sign(message.as_slice()).to_bytes();
    inputs.extend((0..4).map(|_| VerifyInput {
        public_key: off_curve,
        signature: good_s,
        message: message.as_slice(),
    }));

    let mut verifier = Zip215Verifier::with_cache(HotKeyCache::with_capacity(16));
    let mut out = vec![false; inputs.len()];
    verifier.verify_batch(&inputs, &mut out);

    assert!(
        out.iter().all(|&valid| !valid),
        "every lane must be rejected"
    );
    assert_eq!(
        resident_count(verifier.cache(), &decodable_keys),
        4,
        "keys that decoded must be retained even when no lane is accepted"
    );
    assert!(
        verifier.cache().get(&off_curve).is_none(),
        "a key that failed to decode must not be retained"
    );
}

/// Compare preseeded scalar-built tables with cold AVX-512-built tables.
#[test]
fn preseeded_cache_tables_match_cold_simd_decoding() {
    let message = b"pre-seeded table agreement".to_vec();
    let mut cases: Vec<Case> = (0..8u64)
        .map(|i| {
            let signing_key = signing_key_from_index(0xcac4_0000 + i);
            Case {
                public_key: <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key)),
                signature: signing_key.sign(&message).to_bytes(),
                message: message.clone(),
            }
        })
        .collect();
    // Tamper two lanes so the paths have to agree on rejections too.
    cases[2].signature[40] ^= 1;
    cases[5].signature[0] ^= 1;
    let expected = [true, true, false, true, true, false, true, true];

    let inputs: Vec<VerifyInput<'_>> = cases.iter().map(Case::input).collect();
    for policy in [VerifyPolicy::Zip215, VerifyPolicy::Dalek] {
        let mut cache = HotKeyCache::with_capacity(inputs.len());
        for case in &cases {
            cache.insert(CachedPublicKey::from_encoded(case.public_key).expect("key decodes"));
        }
        // Every lane is a hit, so no lane falls back to the SIMD builder.
        let mut preseeded = RuntimeVerifier::with_cache(policy, cache);
        let mut preseeded_out = vec![false; inputs.len()];
        preseeded.verify_batch(&inputs, &mut preseeded_out);

        let mut cold = RuntimeVerifier::with_cache(policy, NullKeyCache::new());
        let mut cold_out = vec![false; inputs.len()];
        cold.verify_batch(&inputs, &mut cold_out);

        assert_eq!(preseeded_out, expected, "{policy:?} pre-seeded tables");
        assert_eq!(cold_out, expected, "{policy:?} cold SIMD decode");
    }
}

#[test]
fn from_encoded_rejects_a_key_that_does_not_decompress() {
    assert!(CachedPublicKey::from_encoded(off_curve_key()).is_none());
}

#[test]
fn verifier_exposes_cache_mut_and_policy() {
    let keys: Vec<[u8; PUBLIC_KEY_LEN]> = (0..4u64)
        .map(|i| <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key_from_index(i))))
        .collect();
    let mut verifier = DalekVerifier::with_cache(HotKeyCache::with_capacity(4));
    assert_eq!(verifier.policy(), VerifyPolicy::Dalek);

    for key in &keys {
        verifier
            .cache_mut()
            .insert(CachedPublicKey::from_encoded(*key).unwrap());
    }
    assert_eq!(resident_count(verifier.cache(), &keys), 4);
    verifier.cache_mut().set_capacity(2);
    assert!(verifier.cache().get(&keys[2]).is_some());
    assert!(verifier.cache().get(&keys[3]).is_some());
    verifier.cache_mut().set_capacity(0);
    assert_eq!(resident_count(verifier.cache(), &keys), 1);

    let zip215_verifier = Zip215Verifier::with_cache(HotKeyCache::with_capacity(1024));
    assert_eq!(zip215_verifier.policy(), VerifyPolicy::Zip215);
}

#[test]
fn default_verifier_does_not_retain_keys() {
    let message = b"default null cache";
    let signing_key = signing_key_from_index(0x0d3f_a017);
    let public_key = <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key));
    let mut verifier = Zip215Verifier::new();
    let input = VerifyInput {
        public_key,
        signature: signing_key.sign(message).to_bytes(),
        message,
    };
    let mut out = [false];

    verifier.verify_batch(&[input], &mut out);

    assert_eq!(out, [true]);
    assert!(verifier.cache().get(&public_key).is_none());
}
