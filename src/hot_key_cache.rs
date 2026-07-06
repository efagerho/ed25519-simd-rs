use crate::batch::PUBLIC_KEY_LEN;
use crate::cache::{CachedPublicKey, KeyCache};
use std::cell::Cell;
use std::collections::HashMap;

/// Eligible eviction candidates sampled per eviction.
const EVICTION_SAMPLE: usize = 8;

/// Point-in-time [`HotKeyCache`] counters and occupancy.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CacheStats {
    /// Total resident keys, including pinned ones.
    pub keys: usize,
    /// Resident keys pinned by [`HotKeyCache::preload`]; not counted against `capacity`.
    pub pinned_keys: usize,
    /// Evictable-key capacity, or `None` for unbounded. Pinned keys may exceed it.
    pub capacity: Option<usize>,
    /// Lane-level [`KeyCache::get`] calls that found a resident key.
    pub hits: u64,
    /// Newly decoded keys inserted, cumulative across evictions.
    pub inserts: u64,
    /// Total keys evicted to stay within `capacity`.
    pub evictions: u64,
}

#[derive(Clone, Debug)]
struct CacheEntry {
    key: CachedPublicKey,
    uses: Cell<u64>,
    last_used: Cell<u64>,
    pinned: Cell<bool>,
}

/// A [`KeyCache`] that retains hot decoded keys across batches.
#[derive(Debug)]
pub struct HotKeyCache {
    keys: HashMap<[u8; PUBLIC_KEY_LEN], CacheEntry>,
    capacity: Option<usize>,
    pinned_keys: usize,
    hits: Cell<u64>,
    inserts: Cell<u64>,
    evictions: Cell<u64>,
    clock: Cell<u64>,
}

impl Default for HotKeyCache {
    fn default() -> Self {
        Self::new()
    }
}

impl HotKeyCache {
    /// Create an unbounded cache.
    pub fn new() -> Self {
        Self {
            keys: HashMap::new(),
            capacity: None,
            pinned_keys: 0,
            hits: Cell::new(0),
            inserts: Cell::new(0),
            evictions: Cell::new(0),
            clock: Cell::new(0),
        }
    }

    /// Create a cache bounded to at least one evictable retained key.
    ///
    /// Preloaded keys are pinned and do not count as evictable capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        let mut cache = Self::new();
        cache.set_capacity(Some(capacity));
        cache
    }

    /// Set the maximum evictable retained key count, or `None` for an unbounded cache.
    ///
    /// Preloaded keys are pinned and may make total occupancy exceed this value.
    pub fn set_capacity(&mut self, capacity: Option<usize>) {
        self.capacity = capacity.map(|capacity| capacity.max(1));
        self.evict_to_capacity(None);
    }

    /// Return cache counters and occupancy.
    pub fn stats(&self) -> CacheStats {
        CacheStats {
            keys: self.keys.len(),
            pinned_keys: self.pinned_keys,
            capacity: self.capacity,
            hits: self.hits.get(),
            inserts: self.inserts.get(),
            evictions: self.evictions.get(),
        }
    }

    /// Return up to `limit` keys ordered by hit count and recent use.
    pub fn hot_public_keys(&self, limit: usize) -> Vec<[u8; PUBLIC_KEY_LEN]> {
        let mut entries: Vec<&CacheEntry> = self.keys.values().collect();
        entries.sort_by(|lhs, rhs| {
            rhs.uses
                .get()
                .cmp(&lhs.uses.get())
                .then_with(|| rhs.last_used.get().cmp(&lhs.last_used.get()))
        });
        entries
            .into_iter()
            .take(limit)
            .map(|entry| entry.key.encoded)
            .collect()
    }

    /// Decode and pin keys outside the eviction bound, returning undecodable
    /// keys in input order.
    ///
    /// Pins do not expire; call [`HotKeyCache::unpin`] for rotated-out key sets.
    #[must_use]
    pub fn preload(&mut self, keys: &[[u8; PUBLIC_KEY_LEN]]) -> Vec<[u8; PUBLIC_KEY_LEN]> {
        keys.iter()
            .copied()
            .filter(|key| !self.insert_encoded(*key, true))
            .collect()
    }

    /// Release pins; keys stay resident until normal eviction. Missing or
    /// unpinned keys are ignored.
    pub fn unpin(&mut self, keys: &[[u8; PUBLIC_KEY_LEN]]) {
        for key in keys {
            if let Some(entry) = self.keys.get(key)
                && entry.pinned.replace(false)
            {
                self.pinned_keys -= 1;
            }
        }
        self.evict_to_capacity(None);
    }

    fn tick(&self) -> u64 {
        let next = self.clock.get().wrapping_add(1);
        self.clock.set(next);
        next
    }

    fn insert_encoded(&mut self, encoded: [u8; PUBLIC_KEY_LEN], pinned: bool) -> bool {
        if let Some(entry) = self.keys.get(&encoded) {
            self.record_use(entry, false);
            if pinned && !entry.pinned.replace(true) {
                self.pinned_keys += 1;
            }
            return true;
        }

        let Some(key) = CachedPublicKey::from_encoded(encoded) else {
            return false;
        };
        self.record_miss(key, pinned);
        true
    }

    /// Update resident-key recency; only [`KeyCache::get`] increments public hits.
    fn record_use(&self, entry: &CacheEntry, count_hit: bool) {
        let last_used = self.tick();
        if count_hit {
            self.hits.set(self.hits.get().wrapping_add(1));
        }
        entry.uses.set(entry.uses.get().wrapping_add(1));
        entry.last_used.set(last_used);
    }

    /// Record a decoded miss and evict if over capacity.
    fn record_miss(&mut self, key: CachedPublicKey, pinned: bool) {
        let last_used = self.tick();
        let encoded = key.encoded;
        if pinned {
            self.pinned_keys += 1;
        }
        self.keys.insert(
            encoded,
            CacheEntry {
                key,
                uses: Cell::new(1),
                last_used: Cell::new(last_used),
                pinned: Cell::new(pinned),
            },
        );
        self.inserts.set(self.inserts.get().wrapping_add(1));
        self.evict_to_capacity(Some(encoded));
    }

    fn evict_to_capacity(&mut self, protected: Option<[u8; PUBLIC_KEY_LEN]>) {
        let Some(capacity) = self.capacity else {
            return;
        };

        while self.evictable_len() > capacity {
            // Sample eligible victims instead of scanning the whole map; filter
            // before `take` so pinned/protected entries do not hide candidates.
            let victim = self
                .keys
                .iter()
                .filter(|(encoded, entry)| Some(**encoded) != protected && !entry.pinned.get())
                .take(EVICTION_SAMPLE)
                .min_by_key(|(_, entry)| (entry.uses.get(), entry.last_used.get()))
                .map(|(encoded, _)| *encoded);

            let Some(victim) = victim else {
                break;
            };
            self.keys.remove(&victim);
            self.evictions.set(self.evictions.get().wrapping_add(1));
        }
    }

    fn evictable_len(&self) -> usize {
        debug_assert!(self.pinned_keys <= self.keys.len());
        self.keys.len() - self.pinned_keys
    }
}

impl crate::cache::private::Sealed for HotKeyCache {}

impl KeyCache for HotKeyCache {
    #[inline]
    fn get(&self, encoded: &[u8; PUBLIC_KEY_LEN]) -> Option<&CachedPublicKey> {
        let entry = self.keys.get(encoded)?;
        self.record_use(entry, true);
        Some(&entry.key)
    }

    fn insert(&mut self, key: CachedPublicKey) {
        if let Some(entry) = self.keys.get(&key.encoded) {
            self.record_use(entry, false);
        } else {
            self.record_miss(key, false);
        }
    }
}
