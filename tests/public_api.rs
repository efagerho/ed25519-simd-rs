mod support;

use curve25519::ed_sigs::VerificationKeyBytes;
use ed25519_simd::{
    CachedPublicKey, HotKeyCache, KeyCache, NullKeyCache, PUBLIC_KEY_LEN, SIGNATURE_LEN, Verifier,
    VerifyInput, VerifyPolicy,
};
use support::{hex_array, signing_key_from_index};

fn rfc8032_key0() -> [u8; PUBLIC_KEY_LEN] {
    hex_array("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
}

fn rfc8032_sig0() -> [u8; SIGNATURE_LEN] {
    hex_array(
        "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155\
         5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
    )
}

fn rfc8032_key1() -> [u8; PUBLIC_KEY_LEN] {
    hex_array("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c")
}

fn rfc8032_sig1() -> [u8; SIGNATURE_LEN] {
    hex_array(
        "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da\
         085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
    )
}

fn resident_count(cache: &HotKeyCache, keys: &[[u8; PUBLIC_KEY_LEN]]) -> usize {
    keys.iter().filter(|key| cache.get(key).is_some()).count()
}

#[test]
fn rejects_mutated_signature() {
    let mut signature = rfc8032_sig0();
    signature[3] ^= 1;
    let input = VerifyInput {
        public_key: rfc8032_key0(),
        signature,
        message: b"",
    };
    let mut out = [true];

    Verifier::new().verify_batch(&[input], &mut out);

    assert_eq!(out, [false]);
}

#[test]
fn cached_verifier_accepts_batch() {
    let input = VerifyInput {
        public_key: rfc8032_key1(),
        signature: rfc8032_sig1(),
        message: &[0x72],
    };
    let mut out = [false];
    let mut verifier = Verifier::with_cache(VerifyPolicy::default(), HotKeyCache::new());

    verifier.verify_batch(&[input], &mut out);

    assert_eq!(out, [true]);
}

#[test]
fn cached_verifier_accepts_simd_sized_batch() {
    let inputs = [VerifyInput {
        public_key: rfc8032_key1(),
        signature: rfc8032_sig1(),
        message: &[0x72],
    }; 8];
    let mut out = [false; 8];
    let mut verifier = Verifier::with_cache(VerifyPolicy::default(), HotKeyCache::new());

    verifier.verify_batch(&inputs, &mut out);

    assert_eq!(out, [true; 8]);
}

#[test]
fn cached_verifier_rejects_one_bad_lane_in_simd_batch() {
    let mut inputs = [VerifyInput {
        public_key: rfc8032_key1(),
        signature: rfc8032_sig1(),
        message: &[0x72],
    }; 8];
    inputs[3].signature[40] ^= 1;
    let mut out = [false; 8];
    let mut verifier = Verifier::with_cache(VerifyPolicy::default(), HotKeyCache::new());

    verifier.verify_batch(&inputs, &mut out);

    assert_eq!(out, [true, true, true, false, true, true, true, true]);
}

#[test]
fn cached_verifier_rejects_bad_r_lane_in_simd_batch() {
    let mut inputs = [VerifyInput {
        public_key: rfc8032_key1(),
        signature: rfc8032_sig1(),
        message: &[0x72],
    }; 8];
    inputs[5].signature[..32].copy_from_slice(&[0xff; 32]);
    let mut out = [false; 8];
    let mut verifier = Verifier::with_cache(VerifyPolicy::default(), HotKeyCache::new());

    verifier.verify_batch(&inputs, &mut out);

    assert_eq!(out, [true, true, true, true, true, false, true, true]);
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

    let mut verifier = Verifier::with_cache(VerifyPolicy::default(), HotKeyCache::new());
    let warm_inputs: Vec<VerifyInput<'_>> = inputs.iter().step_by(2).copied().collect();
    let mut warm_out = vec![false; warm_inputs.len()];
    verifier.verify_batch(&warm_inputs, &mut warm_out);
    assert!(warm_out.iter().all(|&valid| valid));
    let warm_public_keys: Vec<[u8; PUBLIC_KEY_LEN]> =
        public_keys.iter().step_by(2).copied().collect();
    assert_eq!(resident_count(verifier.cache(), &warm_public_keys), 4);

    // Corrupt one hit lane and one miss lane to catch table/lane mix-ups.
    inputs[2].signature[0] ^= 1;
    inputs[3].signature[0] ^= 1;

    let mut out = [false; 8];
    verifier.verify_batch(&inputs, &mut out);
    assert_eq!(out, [true, true, false, false, true, true, true, true]);

    // The previously-missing keys are now cached too (all 8 resident).
    assert_eq!(resident_count(verifier.cache(), &public_keys), 8);
}

#[test]
fn hot_key_cache_retains_recent_keys_with_capacity() {
    let mut cache = HotKeyCache::with_capacity(1);

    cache.insert(CachedPublicKey::from_encoded(rfc8032_key0()).unwrap());
    assert!(cache.get(&rfc8032_key0()).is_some());

    cache.insert(CachedPublicKey::from_encoded(rfc8032_key1()).unwrap());
    assert!(cache.get(&rfc8032_key1()).is_some());
    assert!(cache.get(&rfc8032_key0()).is_none());

    cache.insert(CachedPublicKey::from_encoded(rfc8032_key0()).unwrap());
    assert!(cache.get(&rfc8032_key0()).is_some());
    assert_eq!(resident_count(&cache, &[rfc8032_key0(), rfc8032_key1()]), 1);
}

#[test]
fn hot_key_cache_evicts_down_to_capacity_with_more_candidates_than_the_eviction_sample() {
    let keys: Vec<[u8; PUBLIC_KEY_LEN]> = (0..12u64)
        .map(|i| <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key_from_index(i))))
        .collect();

    let mut cache = HotKeyCache::new();
    for key in &keys {
        cache.insert(CachedPublicKey::from_encoded(*key).unwrap());
    }
    assert_eq!(resident_count(&cache, &keys), 12);

    cache.set_capacity(Some(3));
    assert_eq!(resident_count(&cache, &keys), 3);
}

#[test]
fn hot_key_cache_set_capacity_clamps_and_evicts_immediately() {
    let keys = [rfc8032_key0(), rfc8032_key1()];
    let mut cache = HotKeyCache::new();
    for key in &keys {
        cache.insert(CachedPublicKey::from_encoded(*key).unwrap());
    }
    assert_eq!(resident_count(&cache, &keys), 2);

    cache.set_capacity(Some(0));
    assert_eq!(resident_count(&cache, &keys), 1);

    cache.set_capacity(Some(5));
    assert_eq!(resident_count(&cache, &keys), 1);

    let missing = keys
        .iter()
        .copied()
        .find(|key| cache.get(key).is_none())
        .expect("one key should have been evicted");
    cache.insert(CachedPublicKey::from_encoded(missing).unwrap());
    assert_eq!(resident_count(&cache, &keys), 2);
}

#[test]
fn verifier_exposes_cache_mut_and_policy() {
    let mut verifier = Verifier::with_cache(VerifyPolicy::Dalek, HotKeyCache::new());
    assert_eq!(verifier.policy(), VerifyPolicy::Dalek);

    verifier.cache_mut().set_capacity(Some(1));
    verifier
        .cache_mut()
        .insert(CachedPublicKey::from_encoded(rfc8032_key0()).unwrap());
    verifier
        .cache_mut()
        .insert(CachedPublicKey::from_encoded(rfc8032_key1()).unwrap());
    assert_eq!(
        resident_count(verifier.cache(), &[rfc8032_key0(), rfc8032_key1()]),
        1
    );

    let zip215_verifier = Verifier::with_cache(VerifyPolicy::Zip215, HotKeyCache::new());
    assert_eq!(zip215_verifier.policy(), VerifyPolicy::Zip215);
}

#[test]
fn null_key_cache_is_stateless() {
    assert_eq!(core::mem::size_of::<NullKeyCache>(), 0);
}

#[test]
fn default_verifier_does_not_retain_keys() {
    let mut verifier = Verifier::with_policy(VerifyPolicy::Zip215);
    let input = VerifyInput {
        public_key: rfc8032_key1(),
        signature: rfc8032_sig1(),
        message: &[0x72],
    };
    let mut out = [false];

    verifier.verify_batch(&[input], &mut out);

    assert_eq!(out, [true]);
    assert!(verifier.cache().get(&rfc8032_key1()).is_none());
}
