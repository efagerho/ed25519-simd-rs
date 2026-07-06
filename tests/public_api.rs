mod support;

use curve25519::ed_sigs::VerificationKeyBytes;
use ed25519_simd::{
    CachedPublicKey, HotKeyCache, KeyCache, NullKeyCache, Verifier, VerifyInput, VerifyPolicy,
};
use support::{hex_array, signing_key_from_index};

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
fn hot_key_cache_handles_mixed_hit_and_miss_lanes_in_one_chunk() {
    let signing_keys: Vec<_> = (0..8u64).map(signing_key_from_index).collect();
    let public_keys: Vec<[u8; 32]> = signing_keys
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
    // Preload every other key so half the lanes of the single 8-lane chunk
    // below are cache hits and the other half are genuine cache misses,
    // combined in one call to try_verify_chunk (every other HotKeyCache test
    // is either fully preloaded or fully cold, never both in one chunk).
    let preloaded: Vec<[u8; 32]> = public_keys.iter().step_by(2).copied().collect();
    assert!(verifier.cache_mut().preload(&preloaded).is_empty());
    assert_eq!(verifier.cache().stats().keys, 4);

    // Corrupt one hit lane (index 2) and one miss lane (index 3) so the test
    // proves each lane's decoded table is matched to that lane's own key,
    // not swapped with a neighboring hit/miss lane during the per-lane merge.
    inputs[2].signature[0] ^= 1;
    inputs[3].signature[0] ^= 1;

    let mut out = [false; 8];
    verifier.verify_batch(&inputs, &mut out);
    assert_eq!(out, [true, true, false, false, true, true, true, true]);

    // The previously-missing keys are now cached too (all 8 resident).
    assert_eq!(verifier.cache().stats().keys, 8);
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
    // Same-chunk duplicate insertions do not count as cache hits; hits are
    // reserved for resident keys found by the verifier's initial lookup pass.
    assert_eq!(stats.hits, 0);
    assert_eq!(verifier.cache().hot_public_keys(1), [rfc8032_key1()]);

    assert!(verifier.cache_mut().preload(&[rfc8032_key0()]).is_empty());
    let stats = verifier.cache().stats();
    assert_eq!(stats.keys, 2);
    assert_eq!(stats.pinned_keys, 1);
    assert_eq!(stats.evictions, 1);
    assert_eq!(stats.inserts, 3);
    let hot_keys = verifier.cache().hot_public_keys(2);
    assert!(hot_keys.contains(&rfc8032_key0()));
    assert!(hot_keys.contains(&rfc8032_key1()));

    // A key already resident and re-preloaded is neither a fresh insert nor a
    // cache hit; only `get` calls contribute to `CacheStats::hits`.
    assert!(verifier.cache_mut().preload(&[rfc8032_key0()]).is_empty());
    let stats = verifier.cache().stats();
    assert_eq!(stats.keys, 2);
    assert_eq!(stats.inserts, 3);
    assert_eq!(stats.hits, 0);

    verifier.verify_batch(&[input0], &mut out);
    assert_eq!(out, [true]);
    let stats = verifier.cache().stats();
    assert_eq!(stats.keys, 2);
    assert_eq!(stats.evictions, 1);
    assert_eq!(stats.hits, 8);
    assert_eq!(verifier.cache().hot_public_keys(1), [rfc8032_key0()]);
}

#[test]
fn hot_key_cache_preload_can_pin_an_already_resident_key() {
    let mut cache = HotKeyCache::new();
    cache.insert(CachedPublicKey::from_encoded(rfc8032_key0()).unwrap());
    let stats = cache.stats();
    assert_eq!(stats.keys, 1);
    assert_eq!(stats.pinned_keys, 0);
    assert_eq!(stats.inserts, 1);

    // Preloading an already-resident, not-yet-pinned key pins it in place
    // instead of inserting a duplicate entry.
    assert!(cache.preload(&[rfc8032_key0()]).is_empty());
    let stats = cache.stats();
    assert_eq!(stats.keys, 1);
    assert_eq!(stats.pinned_keys, 1);
    assert_eq!(stats.inserts, 1);

    // Preloading it again (already pinned) doesn't double-count.
    assert!(cache.preload(&[rfc8032_key0()]).is_empty());
    assert_eq!(cache.stats().pinned_keys, 1);
}

#[test]
fn hot_key_cache_evicts_down_to_capacity_with_more_candidates_than_the_eviction_sample() {
    // Eviction bounds each round's scan to a fixed-size sample (currently 8)
    // instead of examining every candidate; use enough evictable candidates
    // that a single round can't see them all, so this exercises the sampling
    // path (never reached by any batch/preload test, which all stay small).
    let keys: Vec<[u8; 32]> = (0..12u64)
        .map(|i| <[u8; 32]>::from(VerificationKeyBytes::from(&signing_key_from_index(i))))
        .collect();

    let mut cache = HotKeyCache::new();
    // Pin two keys so they must survive untouched even while many more
    // evictable candidates than the sample size compete for the rest.
    assert!(cache.preload(&keys[..2]).is_empty());
    for key in &keys[2..] {
        cache.insert(CachedPublicKey::from_encoded(*key).unwrap());
    }
    assert_eq!(cache.stats().keys, 12);
    assert_eq!(cache.stats().pinned_keys, 2);

    // Shrink the evictable capacity well below the 10 evictable candidates,
    // forcing several eviction rounds in a row.
    cache.set_capacity(Some(3));
    let stats = cache.stats();
    assert_eq!(stats.capacity, Some(3));
    assert_eq!(stats.pinned_keys, 2);
    assert_eq!(stats.keys - stats.pinned_keys, 3);
    assert_eq!(stats.evictions, 10 - 3);
    for key in &keys[..2] {
        assert!(cache.get(key).is_some(), "pinned key must survive eviction");
    }
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

    let mut cache = HotKeyCache::with_capacity(1);
    assert!(cache.preload(&[rfc8032_key0()]).is_empty());
    cache.insert(CachedPublicKey::from_encoded(rfc8032_key1()).unwrap());
    let stats = cache.stats();
    assert_eq!(stats.capacity, Some(1));
    assert_eq!(stats.keys, 2);
    assert_eq!(stats.pinned_keys, 1);
    assert_eq!(stats.evictions, 0);
}

#[test]
fn hot_key_cache_unpin_releases_capacity() {
    let mut cache = HotKeyCache::with_capacity(1);
    assert!(cache.preload(&[rfc8032_key0()]).is_empty());
    cache.insert(CachedPublicKey::from_encoded(rfc8032_key1()).unwrap());
    let stats = cache.stats();
    assert_eq!(stats.keys, 2);
    assert_eq!(stats.pinned_keys, 1);
    assert_eq!(stats.evictions, 0, "a pinned key must not be evicted by another insert");

    // Unpinning key0 makes it an ordinary evictable entry again; `unpin`
    // reclaims capacity immediately rather than waiting for the next insert.
    cache.unpin(&[rfc8032_key0()]);
    let stats = cache.stats();
    assert_eq!(stats.pinned_keys, 0);
    assert_eq!(stats.keys, 1);
    assert_eq!(stats.evictions, 1);
    assert!(cache.get(&rfc8032_key1()).is_some());
    assert!(cache.get(&rfc8032_key0()).is_none());

    // Unpinning an absent/never-pinned key is a harmless no-op.
    cache.unpin(&[rfc8032_key0()]);
    assert_eq!(cache.stats().pinned_keys, 0);
    assert_eq!(cache.stats().evictions, 1);
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
