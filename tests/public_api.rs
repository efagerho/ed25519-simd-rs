mod support;

use ed25519_simd::{
    CachedPublicKey, HotKeyCache, KeyCache, NullKeyCache, Verifier, VerifyInput, VerifyPolicy,
};
use support::hex_array;

fn rfc8032_key0() -> [u8; 32] {
    hex_array("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
}

fn rfc8032_sig0() -> [u8; 64] {
    hex_array(
        "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155\
         5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
    )
}

fn rfc8032_key1() -> [u8; 32] {
    hex_array("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c")
}

fn rfc8032_sig1() -> [u8; 64] {
    hex_array(
        "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da\
         085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
    )
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

    assert!(verifier.cache_mut().preload(&[rfc8032_key1()]).is_empty());
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

    assert!(verifier.cache_mut().preload(&[rfc8032_key1()]).is_empty());
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

    assert!(verifier.cache_mut().preload(&[rfc8032_key1()]).is_empty());
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

    assert!(verifier.cache_mut().preload(&[rfc8032_key1()]).is_empty());
    verifier.verify_batch(&inputs, &mut out);

    assert_eq!(out, [true, true, true, true, true, false, true, true]);
}

#[test]
fn hot_key_cache_tracks_hot_keys_and_capacity() {
    let input0 = VerifyInput {
        public_key: rfc8032_key0(),
        signature: rfc8032_sig0(),
        message: b"",
    };
    let input1 = VerifyInput {
        public_key: rfc8032_key1(),
        signature: rfc8032_sig1(),
        message: &[0x72],
    };
    let mut verifier = Verifier::with_cache(VerifyPolicy::default(), HotKeyCache::with_capacity(1));
    let mut out = [false];

    verifier.verify_batch(&[input0], &mut out);
    assert_eq!(out, [true]);
    verifier.verify_batch(&[input1], &mut out);
    assert_eq!(out, [true]);

    let stats = verifier.cache().stats();
    assert_eq!(stats.keys, 1);
    assert_eq!(stats.capacity, Some(1));
    assert_eq!(stats.evictions, 1);
    assert_eq!(stats.inserts, 2);
    assert_eq!(stats.misses, 2);
    // Each single-input batch is padded to a full SIMD chunk of 8 identical
    // lanes; the verifier looks up and inserts every lane independently (it
    // has no notion of "this lane is a padding duplicate"), so the 7 padding
    // lanes per batch each land as a hit against the entry the first lane
    // just inserted.
    assert_eq!(stats.hits, 14);
    assert_eq!(verifier.cache().hot_public_keys(1), [rfc8032_key1()]);

    assert!(verifier.cache_mut().preload(&[rfc8032_key0()]).is_empty());
    let stats = verifier.cache().stats();
    assert_eq!(stats.keys, 1);
    assert_eq!(stats.pinned_keys, 1);
    assert_eq!(stats.evictions, 2);
    assert_eq!(stats.inserts, 3);
    assert_eq!(stats.misses, 3);
    assert_eq!(verifier.cache().hot_public_keys(1), [rfc8032_key0()]);

    // A key already resident and re-preloaded is a hit, not a fresh insert.
    assert!(verifier.cache_mut().preload(&[rfc8032_key0()]).is_empty());
    let stats = verifier.cache().stats();
    assert_eq!(stats.keys, 1);
    assert_eq!(stats.inserts, 3);
    assert_eq!(stats.hits, 15);
}

#[test]
fn hot_key_cache_set_capacity_clamps_and_evicts_immediately() {
    let mut cache = HotKeyCache::new();
    cache.insert(CachedPublicKey::from_encoded(rfc8032_key0()).unwrap());
    cache.insert(CachedPublicKey::from_encoded(rfc8032_key1()).unwrap());
    assert_eq!(cache.stats().keys, 2);
    assert_eq!(cache.stats().capacity, None);

    // A requested capacity of 0 is clamped up to 1, and the cache evicts down
    // to it immediately rather than waiting for the next insert.
    cache.set_capacity(Some(0));
    let stats = cache.stats();
    assert_eq!(stats.capacity, Some(1));
    assert_eq!(stats.keys, 1);
    assert_eq!(stats.evictions, 1);

    // Raising the capacity back up does not evict or insert anything.
    cache.set_capacity(Some(5));
    let stats = cache.stats();
    assert_eq!(stats.capacity, Some(5));
    assert_eq!(stats.keys, 1);
    assert_eq!(stats.evictions, 1);
}

#[test]
fn verifier_exposes_cache_mut_and_policy() {
    let mut verifier = Verifier::with_cache(VerifyPolicy::Dalek, HotKeyCache::new());
    assert_eq!(verifier.policy(), VerifyPolicy::Dalek);
    assert_eq!(verifier.cache().stats().capacity, None);

    verifier.cache_mut().set_capacity(Some(1));
    assert_eq!(verifier.cache().stats().capacity, Some(1));

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
