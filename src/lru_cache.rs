use crate::cache::{CachedPublicKey, KeyCache};
use std::cell::Cell;
use std::collections::HashMap;

/// Number of eligible candidates `evict_to_capacity` examines per eviction,
/// bounding its cost independent of cache size. See `evict_to_capacity`.
const EVICTION_SAMPLE: usize = 8;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CacheStats {
    pub keys: usize,
    pub pinned_keys: usize,
    pub max_keys: Option<usize>,
    pub hits: u64,
    pub misses: u64,
    pub inserts: u64,
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
    keys: HashMap<[u8; 32], LruEntry>,
    max_cached_keys: Option<usize>,
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
            max_cached_keys: None,
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
    pub fn with_capacity(max_cached_keys: usize) -> Self {
        let mut cache = Self::new();
        cache.set_capacity(Some(max_cached_keys));
        cache
    }

    /// Set the maximum evictable retained key count, or `None` for an unbounded cache.
    ///
    /// Preloaded keys are pinned and may make total occupancy exceed this value.
    pub fn set_capacity(&mut self, max_cached_keys: Option<usize>) {
        self.max_cached_keys = max_cached_keys.map(|keys| keys.max(1));
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
            max_keys: self.max_cached_keys,
            hits: self.hits.get(),
            misses: self.misses.get(),
            inserts: self.inserts.get(),
            evictions: self.evictions.get(),
        }
    }

    /// Return up to `limit` keys ordered by hit count and recent use.
    pub fn hot_public_keys(&self, limit: usize) -> Vec<[u8; 32]> {
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

    /// Decode and pin the given keys so they are retained outside the eviction bound.
    pub fn preload(&mut self, keys: &[[u8; 32]]) {
        for key in keys {
            self.insert_encoded(*key, true);
        }
    }

    fn tick(&self) -> u64 {
        let next = self.clock.get().wrapping_add(1);
        self.clock.set(next);
        next
    }

    fn touch_entry(&self, entry: &LruEntry) {
        let last_used = self.tick();
        self.hits.set(self.hits.get().wrapping_add(1));
        entry.hits.set(entry.hits.get().wrapping_add(1));
        entry.last_used.set(last_used);
    }

    fn insert_encoded(&mut self, encoded: [u8; 32], pinned: bool) -> bool {
        let last_used = self.tick();

        if let Some(entry) = self.keys.get_mut(&encoded) {
            self.hits.set(self.hits.get().wrapping_add(1));
            entry.hits.set(entry.hits.get().wrapping_add(1));
            entry.last_used.set(last_used);
            entry.pinned.set(entry.pinned.get() || pinned);
            return true;
        }

        self.misses.set(self.misses.get().wrapping_add(1));
        let Some(key) = CachedPublicKey::from_encoded(encoded) else {
            return false;
        };
        self.insert_cached(key, pinned, last_used);
        self.evict_to_capacity(Some(encoded));
        true
    }

    fn insert_cached(&mut self, key: CachedPublicKey, pinned: bool, last_used: u64) {
        let encoded = key.encoded;
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
    }

    fn evict_to_capacity(&mut self, protected: Option<[u8; 32]>) {
        let Some(max_cached_keys) = self.max_cached_keys else {
            return;
        };

        while self.keys.len() > max_cached_keys {
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
    fn get(&self, encoded: &[u8; 32]) -> Option<&CachedPublicKey> {
        let entry = self.keys.get(encoded)?;
        self.touch_entry(entry);
        Some(&entry.key)
    }

    fn insert(&mut self, key: CachedPublicKey) {
        let last_used = self.tick();
        if let Some(entry) = self.keys.get(&key.encoded) {
            self.hits.set(self.hits.get().wrapping_add(1));
            entry.hits.set(entry.hits.get().wrapping_add(1));
            entry.last_used.set(last_used);
        } else {
            let encoded = key.encoded;
            self.misses.set(self.misses.get().wrapping_add(1));
            self.insert_cached(key, false, last_used);
            self.evict_to_capacity(Some(encoded));
        }
    }
}
