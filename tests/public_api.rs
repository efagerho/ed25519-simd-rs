mod support;

use ed25519_simd::{
    CachedPublicKey, KeyCache, LruKeyCache, NullKeyCache, Verifier, VerifyInput, VerifyPolicy,
};
use std::cell::Cell;
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
    let mut verifier = Verifier::with_cache(VerifyPolicy::default(), LruKeyCache::new());

    verifier.preload_public_keys(&[rfc8032_key1()]);
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
    let mut verifier = Verifier::with_cache(VerifyPolicy::default(), LruKeyCache::new());

    verifier.preload_public_keys(&[rfc8032_key1()]);
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
    let mut verifier = Verifier::with_cache(VerifyPolicy::default(), LruKeyCache::new());

    verifier.preload_public_keys(&[rfc8032_key1()]);
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
    let mut verifier = Verifier::with_cache(VerifyPolicy::default(), LruKeyCache::new());

    verifier.preload_public_keys(&[rfc8032_key1()]);
    verifier.verify_batch(&inputs, &mut out);

    assert_eq!(out, [true, true, true, true, true, false, true, true]);
}

#[test]
fn lru_cache_tracks_hot_keys_and_capacity() {
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
    let mut verifier = Verifier::with_cache_capacity(VerifyPolicy::default(), 1);
    let mut out = [false];

    verifier.verify_batch(&[input0], &mut out);
    assert_eq!(out, [true]);
    verifier.verify_batch(&[input1], &mut out);
    assert_eq!(out, [true]);

    let stats = verifier.cache().stats();
    assert_eq!(stats.keys, 1);
    assert_eq!(stats.evictions, 1);
    assert_eq!(verifier.cache().hot_public_keys(1), [rfc8032_key1()]);

    verifier.preload_public_keys(&[rfc8032_key0()]);
    let stats = verifier.cache().stats();
    assert_eq!(stats.keys, 1);
    assert_eq!(stats.pinned_keys, 1);
    assert_eq!(verifier.cache().hot_public_keys(1), [rfc8032_key0()]);
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

#[derive(Default)]
struct TinyKeyCache {
    keys: Vec<CachedPublicKey>,
    hits: Cell<u64>,
}

impl KeyCache for TinyKeyCache {
    fn get(&self, encoded: &[u8; 32]) -> Option<&CachedPublicKey> {
        let key = self.keys.iter().find(|key| &key.encoded == encoded);
        if key.is_some() {
            self.hits.set(self.hits.get() + 1);
        }
        key
    }

    fn insert(&mut self, key: CachedPublicKey) {
        if self.keys.iter().all(|cached| cached.encoded != key.encoded) && self.keys.len() < 2 {
            self.keys.push(key);
        }
    }
}

#[test]
fn custom_key_cache_can_retain_a_small_hot_set() {
    let input = VerifyInput {
        public_key: rfc8032_key1(),
        signature: rfc8032_sig1(),
        message: &[0x72],
    };
    let mut verifier = Verifier::with_cache(VerifyPolicy::Zip215, TinyKeyCache::default());
    let mut out = [false];

    verifier.verify_batch(&[input], &mut out);
    assert_eq!(out, [true]);
    assert_eq!(verifier.cache().keys.len(), 1);

    verifier.verify_batch(&[input], &mut out);
    assert_eq!(out, [true]);
    assert_eq!(verifier.cache().hits.get(), 1);
}
