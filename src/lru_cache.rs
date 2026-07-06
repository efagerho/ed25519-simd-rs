use crate::batch::PUBLIC_KEY_LEN;
use crate::cache::{CachedPublicKey, KeyCache};
use std::cell::Cell;
use std::collections::HashMap;

/// Number of eligible candidates `evict_to_capacity` examines per eviction,
/// bounding its cost independent of cache size. See `evict_to_capacity`.
const EVICTION_SAMPLE: usize = 8;

/// Snapshot of an [`LruKeyCache`]'s counters and occupancy at the moment
/// [`LruKeyCache::stats`] was called.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CacheStats {
    /// Total resident keys, including pinned ones.
    pub keys: usize,
    /// Resident keys pinned by [`LruKeyCache::preload`]; not counted against `capacity`.
    pub pinned_keys: usize,
    /// The evictable capacity passed to [`LruKeyCache::with_capacity`]/[`LruKeyCache::set_capacity`],
    /// or `None` for an unbounded cache. Pinned keys may push `keys` above this.
    pub capacity: Option<usize>,
    /// Total [`KeyCache::get`]/[`KeyCache::insert`] calls that found a resident key.
    pub hits: u64,
    /// Total [`KeyCache::get`]/[`KeyCache::insert`] calls that found no resident key.
    pub misses: u64,
    /// Total keys newly decoded and inserted (cumulative; not reduced by eviction).
    pub inserts: u64,
    /// Total keys evicted to stay within `capacity`.
    pub evictions: u64,
}

#[derive(Clone, Debug)]
struct LruEntry {
    key: CachedPublicKey,
    hits: Cell<u64>,
    last_used: Cell<u64>,
    pinned: Cell<bool>,
}

/// A provided [`KeyCache`]: keeps decoded keys in a map across batches, with
/// optional capacity and least-valuable eviction. Best for workloads with a hot
/// set of repeating keys.
#[derive(Debug)]
pub struct LruKeyCache {
    keys: HashMap<[u8; PUBLIC_KEY_LEN], LruEntry>,
    capacity: Option<usize>,
    hits: Cell<u64>,
    misses: Cell<u64>,
    inserts: Cell<u64>,
    evictions: Cell<u64>,
    clock: Cell<u64>,
}

impl Default for LruKeyCache {
    fn default() -> Self {
        Self::new()
    }
}

impl LruKeyCache {
    /// Create an unbounded cache.
    pub fn new() -> Self {
        Self {
            keys: HashMap::new(),
            capacity: None,
            hits: Cell::new(0),
            misses: Cell::new(0),
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
            pinned_keys: self
                .keys
                .values()
                .filter(|entry| entry.pinned.get())
                .count(),
            capacity: self.capacity,
            hits: self.hits.get(),
            misses: self.misses.get(),
            inserts: self.inserts.get(),
            evictions: self.evictions.get(),
        }
    }

    /// Return up to `limit` keys ordered by hit count and recent use.
    pub fn hot_public_keys(&self, limit: usize) -> Vec<[u8; PUBLIC_KEY_LEN]> {
        let mut entries: Vec<&LruEntry> = self.keys.values().collect();
        entries.sort_by(|lhs, rhs| {
            rhs.hits
                .get()
                .cmp(&lhs.hits.get())
                .then_with(|| rhs.last_used.get().cmp(&lhs.last_used.get()))
        });
        entries
            .into_iter()
            .take(limit)
            .map(|entry| entry.key.encoded)
            .collect()
    }

    /// Decode and pin the given keys so they are retained outside the eviction
    /// bound. Returns the keys that failed to decode (and so were not
    /// pinned), in the order given; an empty vector means every key succeeded.
    #[must_use]
    pub fn preload(&mut self, keys: &[[u8; PUBLIC_KEY_LEN]]) -> Vec<[u8; PUBLIC_KEY_LEN]> {
        keys.iter()
            .copied()
            .filter(|key| !self.insert_encoded(*key, true))
            .collect()
    }

    fn tick(&self) -> u64 {
        let next = self.clock.get().wrapping_add(1);
        self.clock.set(next);
        next
    }

    fn insert_encoded(&mut self, encoded: [u8; PUBLIC_KEY_LEN], pinned: bool) -> bool {
        if let Some(entry) = self.keys.get(&encoded) {
            self.touch_entry(entry);
            if pinned {
                entry.pinned.set(true);
            }
            return true;
        }

        let Some(key) = CachedPublicKey::from_encoded(encoded) else {
            return false;
        };
        self.record_miss(key, pinned);
        true
    }

    /// Shared hit-bookkeeping for a key already resident in the cache. See
    /// `record_miss` for the counterpart shared by the two insertion paths
    /// (`insert_encoded` and the `KeyCache::insert` impl below).
    fn touch_entry(&self, entry: &LruEntry) {
        let last_used = self.tick();
        self.hits.set(self.hits.get().wrapping_add(1));
        entry.hits.set(entry.hits.get().wrapping_add(1));
        entry.last_used.set(last_used);
    }

    /// Shared miss-bookkeeping: record the decoded key and evict if over
    /// capacity. See `touch_entry` for the hit counterpart.
    fn record_miss(&mut self, key: CachedPublicKey, pinned: bool) {
        let last_used = self.tick();
        let encoded = key.encoded;
        self.misses.set(self.misses.get().wrapping_add(1));
        self.keys.insert(
            encoded,
            LruEntry {
                key,
                hits: Cell::new(1),
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

        while self.keys.len() > capacity {
            // Bound the scan to a fixed-size sample of eligible candidates
            // instead of the whole map, the same approximation production
            // caches (e.g. Redis's `maxmemory-samples`) make to keep eviction
            // cost independent of cache size. `take` comes after `filter` so
            // a sample skewed toward pinned/protected entries can't make this
            // give up early while real candidates exist elsewhere; for caches
            // at or under EVICTION_SAMPLE live entries (every case in this
            // crate's tests), it's exactly equivalent to an exhaustive scan.
            let victim = self
                .keys
                .iter()
                .filter(|(encoded, entry)| Some(**encoded) != protected && !entry.pinned.get())
                .take(EVICTION_SAMPLE)
                .min_by_key(|(_, entry)| (entry.hits.get(), entry.last_used.get()))
                .map(|(encoded, _)| *encoded);

            let Some(victim) = victim else {
                break;
            };
            self.keys.remove(&victim);
            self.evictions.set(self.evictions.get().wrapping_add(1));
        }
    }
}

impl KeyCache for LruKeyCache {
    #[inline]
    fn get(&self, encoded: &[u8; PUBLIC_KEY_LEN]) -> Option<&CachedPublicKey> {
        let entry = self.keys.get(encoded)?;
        self.touch_entry(entry);
        Some(&entry.key)
    }

    fn insert(&mut self, key: CachedPublicKey) {
        if let Some(entry) = self.keys.get(&key.encoded) {
            self.touch_entry(entry);
        } else {
            self.record_miss(key, false);
        }
    }
}
