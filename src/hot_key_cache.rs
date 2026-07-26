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

impl CacheEntry {
    /// Stamp this entry with the next clock value.
    fn touch(&self, clock: &Cell<u64>) {
        self.last_used.set(tick(clock));
    }
}

/// Advance the recency clock and return its new value.
fn tick(clock: &Cell<u64>) -> u64 {
    let next = clock.get().wrapping_add(1);
    clock.set(next);
    next
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
        tick(&self.clock)
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
        entry.touch(&self.clock);
        entry.key.hits.set(entry.key.hits.get().saturating_add(1));
        Some(&entry.key)
    }

    fn insert(&mut self, key: CachedPublicKey) {
        if let Some(entry) = self.keys.get_mut(&key.encoded) {
            // Promotion: adopt the upgraded tables (affine main + A′ split).
            if key.table_hi.is_some() && entry.key.table_hi.is_none() {
                entry.key.table = key.table;
                entry.key.table_hi = key.table_hi;
            }
            entry.touch(&self.clock);
        } else {
            // Fresh key: stored as decoded — no normalization, no A′.
            self.insert_cached(key);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::edwards::{EdwardsPoint, PointTable};

    #[test]
    fn split_table_is_lazy_and_adopted_on_reinsert() {
        let encoded = EdwardsPoint::basepoint().compress();
        let mut cache = HotKeyCache::new();
        cache.insert(CachedPublicKey::from_encoded(encoded).expect("valid key"));

        let entry = cache.get(&encoded).expect("just inserted");
        assert!(
            !entry.table.is_affine(),
            "insert must store the table as decoded (lazy normalization)"
        );
        assert!(
            entry.table_hi.is_none(),
            "insert must not build the split table (lazy promotion)"
        );

        // Simulate the verifier's promotion hand-back (both tables upgraded).
        let a_prime = EdwardsPoint::decompress(&encoded)
            .expect("valid key")
            .mul_by_pow2_127();
        let mut upgraded = CachedPublicKey::from_encoded(encoded).expect("valid key");
        upgraded.table = upgraded.table.normalized_affine();
        upgraded.table_hi = Some(PointTable::new(&a_prime).normalized_affine());
        cache.insert(upgraded);

        let entry = cache.get(&encoded).expect("still resident");
        assert!(entry.table.is_affine(), "main table adopted at promotion");
        let hi = entry.table_hi.as_ref().expect("split table adopted");
        assert!(hi.is_affine());
        assert_eq!(
            hi.recover_base_point().compress(),
            a_prime.compress(),
            "adopted table_hi base is not [2^127]A"
        );
    }
}
