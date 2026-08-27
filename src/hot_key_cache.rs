use crate::batch::PUBLIC_KEY_LEN;
use crate::cache::{CachedPublicKey, KeyCache};
use std::cell::Cell;
use std::collections::HashMap;

/// Link sentinel for the ends of the recency list.
const NONE: usize = usize::MAX;

#[derive(Debug)]
struct CacheEntry {
    key: CachedPublicKey,
    // Intrusive recency-list links, as slot indices into `entries`. `newer`
    // runs toward the most-recently-used end.
    newer: Cell<usize>,
    older: Cell<usize>,
}

/// A [`KeyCache`] that retains hot decoded keys across batches, bounded to a
/// caller-chosen capacity and evicting the least recently used key.
///
/// The capacity is mandatory: keys are attacker-supplied, and each retained one
/// costs a few kilobytes, so an unbounded cache is a memory-exhaustion vector.
/// Picking a bound also forces the question this cache only pays off when you
/// can answer — how many keys actually repeat. Without an answer, use
/// [`NullKeyCache`](crate::NullKeyCache) instead.
#[derive(Debug)]
pub struct HotKeyCache {
    // Resident entries in arbitrary slot order, threaded by the recency list
    // below; `index` maps an encoded key to its slot. Recency is tracked by
    // list position rather than a timestamp, so both lookup and eviction are
    // O(1) — eviction cost cannot be amplified by a caller feeding the cache
    // nothing but distinct keys.
    entries: Vec<CacheEntry>,
    index: HashMap<[u8; PUBLIC_KEY_LEN], usize>,
    capacity: usize,
    mru: Cell<usize>,
    lru: Cell<usize>,
}

impl HotKeyCache {
    /// Create a cache bounded to at least one retained key.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            entries: Vec::new(),
            index: HashMap::new(),
            capacity: capacity.max(1),
            mru: Cell::new(NONE),
            lru: Cell::new(NONE),
        }
    }

    /// Set the maximum retained key count, clamped to at least one, evicting
    /// immediately if the cache now exceeds it.
    pub fn set_capacity(&mut self, capacity: usize) {
        self.capacity = capacity.max(1);
        self.evict_to_capacity();
    }

    /// Detach `slot` from the recency list.
    fn unlink(&self, slot: usize) {
        let newer = self.entries[slot].newer.get();
        let older = self.entries[slot].older.get();
        if newer == NONE {
            self.mru.set(older);
        } else {
            self.entries[newer].older.set(older);
        }
        if older == NONE {
            self.lru.set(newer);
        } else {
            self.entries[older].newer.set(newer);
        }
    }

    /// Attach an already-detached `slot` at the most-recently-used end.
    fn link_mru(&self, slot: usize) {
        let previous_mru = self.mru.get();
        self.entries[slot].newer.set(NONE);
        self.entries[slot].older.set(previous_mru);
        if previous_mru == NONE {
            self.lru.set(slot);
        } else {
            self.entries[previous_mru].newer.set(slot);
        }
        self.mru.set(slot);
    }

    fn touch(&self, slot: usize) {
        if self.mru.get() != slot {
            self.unlink(slot);
            self.link_mru(slot);
        }
    }

    /// Evict from the least-recently-used end. The loop only runs while at
    /// least two keys are resident, so the entry just linked as MRU — the key
    /// the current chunk is about to use — is never the victim.
    fn evict_to_capacity(&mut self) {
        while self.entries.len() > self.capacity {
            let lru = self.lru.get();
            debug_assert_ne!(lru, NONE, "a non-empty cache always has an LRU end");
            self.remove_at(lru);
        }
    }

    fn remove_at(&mut self, slot: usize) {
        self.unlink(slot);
        let removed = self.entries.swap_remove(slot);
        self.index.remove(&removed.key.encoded);

        // `swap_remove` moved the former last entry into `slot`. Nothing points
        // at `slot` any more (it was unlinked first), so repointing what
        // referred to the moved entry's old index finishes the move.
        if let Some(moved) = self.entries.get(slot) {
            let (encoded, newer, older) = (moved.key.encoded, moved.newer.get(), moved.older.get());
            self.index.insert(encoded, slot);
            if newer == NONE {
                self.mru.set(slot);
            } else {
                self.entries[newer].older.set(slot);
            }
            if older == NONE {
                self.lru.set(slot);
            } else {
                self.entries[older].newer.set(slot);
            }
        }
    }

    /// Walk the recency list in both directions and cross-check it against
    /// `entries`/`index`, catching any link surgery that left the cache
    /// inconsistent.
    #[cfg(test)]
    fn assert_invariants(&self) {
        assert_eq!(self.entries.len(), self.index.len());
        assert!(self.entries.len() <= self.capacity);
        for (slot, entry) in self.entries.iter().enumerate() {
            assert_eq!(self.index.get(&entry.key.encoded), Some(&slot));
        }

        let mut forward = Vec::new();
        let mut slot = self.mru.get();
        let mut previous = NONE;
        while slot != NONE {
            assert!(slot < self.entries.len());
            assert_eq!(self.entries[slot].newer.get(), previous);
            forward.push(slot);
            previous = slot;
            slot = self.entries[slot].older.get();
        }
        assert_eq!(forward.len(), self.entries.len(), "list length");
        assert_eq!(previous, self.lru.get(), "lru end");

        let mut backward = Vec::new();
        let mut slot = self.lru.get();
        while slot != NONE {
            backward.push(slot);
            slot = self.entries[slot].newer.get();
        }
        backward.reverse();
        assert_eq!(forward, backward, "list is not doubly consistent");
    }
}

impl crate::cache::private::Sealed for HotKeyCache {}

impl KeyCache for HotKeyCache {
    #[inline]
    fn get(&self, encoded: &[u8; PUBLIC_KEY_LEN]) -> Option<&CachedPublicKey> {
        let slot = *self.index.get(encoded)?;
        self.touch(slot);
        Some(&self.entries[slot].key)
    }

    fn insert(&mut self, key: CachedPublicKey) {
        if let Some(&slot) = self.index.get(&key.encoded) {
            self.touch(slot);
            return;
        }

        let slot = self.entries.len();
        self.index.insert(key.encoded, slot);
        self.entries.push(CacheEntry {
            key,
            newer: Cell::new(NONE),
            older: Cell::new(NONE),
        });
        self.link_mru(slot);
        self.evict_to_capacity();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::edwards::{EdwardsPoint, PointTable};
    use rand::{RngCore, SeedableRng, rngs::StdRng};

    /// A distinct cached key per index. The table contents are irrelevant to
    /// cache bookkeeping, so reuse the identity table and vary only `encoded`.
    fn key(index: u64) -> CachedPublicKey {
        let mut encoded = [0u8; PUBLIC_KEY_LEN];
        encoded[..8].copy_from_slice(&index.to_le_bytes());
        CachedPublicKey {
            encoded,
            table: PointTable::new(&EdwardsPoint::identity()),
        }
    }

    fn encoded(index: u64) -> [u8; PUBLIC_KEY_LEN] {
        key(index).encoded
    }

    #[test]
    fn evicts_least_recently_used() {
        let mut cache = HotKeyCache::with_capacity(3);
        for i in 0..3 {
            cache.insert(key(i));
        }
        // Touch 0 and 2, leaving 1 as the LRU.
        assert!(cache.get(&encoded(0)).is_some());
        assert!(cache.get(&encoded(2)).is_some());
        cache.assert_invariants();

        cache.insert(key(3));
        cache.assert_invariants();
        assert!(
            cache.get(&encoded(1)).is_none(),
            "LRU key should be evicted"
        );
        for i in [0, 2, 3] {
            assert!(
                cache.get(&encoded(i)).is_some(),
                "key {i} should be resident"
            );
        }
    }

    #[test]
    fn a_repeatedly_used_hot_set_survives_distinct_key_churn() {
        // The regression this cache exists for: sampling eviction candidates
        // from a fixed window (a `HashMap`'s iteration order, say) evicts hot
        // keys and retains cold ones once the hot set outgrows the window.
        let capacity = 64;
        let hot_count = 48;
        let mut cache = HotKeyCache::with_capacity(capacity);
        for i in 0..hot_count {
            cache.insert(key(i));
        }

        for cold in 1000..3000 {
            for i in 0..hot_count {
                assert!(cache.get(&encoded(i)).is_some(), "hot key {i} was evicted");
            }
            cache.insert(key(cold));
        }
        cache.assert_invariants();
    }

    #[test]
    fn insert_of_a_resident_key_only_refreshes_recency() {
        let mut cache = HotKeyCache::with_capacity(2);
        cache.insert(key(0));
        cache.insert(key(1));
        // Re-inserting 0 must refresh it rather than add a second entry.
        cache.insert(key(0));
        cache.assert_invariants();
        assert_eq!(cache.entries.len(), 2);

        cache.insert(key(2));
        assert!(cache.get(&encoded(1)).is_none(), "1 was the LRU");
        assert!(cache.get(&encoded(0)).is_some());
        assert!(cache.get(&encoded(2)).is_some());
    }

    #[test]
    fn set_capacity_clamps_to_one_and_evicts_immediately() {
        let mut cache = HotKeyCache::with_capacity(8);
        for i in 0..8 {
            cache.insert(key(i));
        }

        cache.set_capacity(3);
        cache.assert_invariants();
        assert_eq!(cache.entries.len(), 3);
        // Shrinking keeps the most recently used keys.
        for i in 5..8 {
            assert!(cache.get(&encoded(i)).is_some(), "key {i} should survive");
        }

        cache.set_capacity(0);
        cache.assert_invariants();
        assert_eq!(cache.entries.len(), 1);
        assert!(
            cache.get(&encoded(7)).is_some(),
            "the MRU key should survive"
        );
    }

    #[test]
    fn capacity_one_keeps_only_the_newest_key() {
        let mut cache = HotKeyCache::with_capacity(1);
        for i in 0..4 {
            cache.insert(key(i));
            cache.assert_invariants();
            assert_eq!(cache.entries.len(), 1);
            assert!(cache.get(&encoded(i)).is_some(), "key {i} just inserted");
        }
    }

    /// Drive interleaved inserts, hits and capacity changes so `swap_remove`
    /// relocates entries from every list position, and check the structure
    /// after each step.
    #[test]
    fn link_surgery_stays_consistent_under_mixed_operations() {
        let mut cache = HotKeyCache::with_capacity(16);
        let mut rng = StdRng::seed_from_u64(0x2545_f491_4f6c_dd1d);

        for step in 0..4096u64 {
            match rng.next_u64() % 4 {
                0 => cache.insert(key(rng.next_u64() % 24)),
                1 => {
                    cache.get(&encoded(rng.next_u64() % 24));
                }
                2 => cache.insert(key(step + 10_000)),
                _ => cache.set_capacity((rng.next_u64() % 20) as usize),
            }
            cache.assert_invariants();
        }
    }
}
