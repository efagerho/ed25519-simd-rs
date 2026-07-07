use crate::batch::PUBLIC_KEY_LEN;
use crate::cache::{CachedPublicKey, KeyCache};
use std::cell::Cell;
use std::collections::HashMap;

/// Eligible eviction candidates sampled per eviction.
const EVICTION_SAMPLE: usize = 8;

#[derive(Clone, Debug)]
struct CacheEntry {
    key: CachedPublicKey,
    last_used: Cell<u64>,
}

/// A [`KeyCache`] that retains hot decoded keys across batches.
#[derive(Debug)]
pub struct HotKeyCache {
    keys: HashMap<[u8; PUBLIC_KEY_LEN], CacheEntry>,
    capacity: Option<usize>,
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
            clock: Cell::new(0),
        }
    }

    /// Create a cache bounded to at least one retained key.
    pub fn with_capacity(capacity: usize) -> Self {
        let mut cache = Self::new();
        cache.set_capacity(Some(capacity));
        cache
    }

    /// Set the maximum retained key count, or `None` for an unbounded cache.
    pub fn set_capacity(&mut self, capacity: Option<usize>) {
        self.capacity = capacity.map(|capacity| capacity.max(1));
        self.evict_to_capacity(None);
    }

    fn tick(&self) -> u64 {
        let next = self.clock.get().wrapping_add(1);
        self.clock.set(next);
        next
    }

    fn touch(&self, entry: &CacheEntry) {
        entry.last_used.set(self.tick());
    }

    fn insert_cached(&mut self, key: CachedPublicKey) {
        let last_used = self.tick();
        let encoded = key.encoded;
        self.keys.insert(
            encoded,
            CacheEntry {
                key,
                last_used: Cell::new(last_used),
            },
        );
        self.evict_to_capacity(Some(encoded));
    }

    fn evict_to_capacity(&mut self, protected: Option<[u8; PUBLIC_KEY_LEN]>) {
        let Some(capacity) = self.capacity else {
            return;
        };

        while self.keys.len() > capacity {
            let victim = self
                .keys
                .iter()
                .filter(|(encoded, _)| Some(**encoded) != protected)
                .take(EVICTION_SAMPLE)
                .min_by_key(|(_, entry)| entry.last_used.get())
                .map(|(encoded, _)| *encoded);

            let Some(victim) = victim else {
                break;
            };
            self.keys.remove(&victim);
        }
    }
}

impl crate::cache::private::Sealed for HotKeyCache {}

impl KeyCache for HotKeyCache {
    #[inline]
    fn get(&self, encoded: &[u8; PUBLIC_KEY_LEN]) -> Option<&CachedPublicKey> {
        let entry = self.keys.get(encoded)?;
        self.touch(entry);
        Some(&entry.key)
    }

    fn insert(&mut self, key: CachedPublicKey) {
        if let Some(entry) = self.keys.get(&key.encoded) {
            self.touch(entry);
        } else {
            self.insert_cached(key);
        }
    }
}
