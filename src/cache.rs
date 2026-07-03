use crate::edwards::{EdwardsPoint, PointTable};

const SIMD_LANES: usize = crate::batch::SIMD_LANES;

/// A decoded public key and its precomputed multiplication table.
#[derive(Clone, Debug)]
pub struct CachedPublicKey {
    pub encoded: [u8; 32],
    pub(crate) table: PointTable,
}

impl CachedPublicKey {
    /// Build a cached public key from its encoded bytes.
    pub fn from_encoded(encoded: [u8; 32]) -> Option<Self> {
        EdwardsPoint::decompress(&encoded).map(|point| Self {
            encoded,
            table: PointTable::new(&point),
        })
    }
}

/// Storage policy for decoded public keys.
///
/// [`NullKeyCache`] retains no decoded keys and is the verifier default.
/// [`LruKeyCache`](crate::LruKeyCache) retains keys across batches for workloads
/// with repeated hot keys. Custom caches can keep an application-owned hot set
/// by storing [`CachedPublicKey`] values. Decoding is owned by the verifier;
/// caches only look up and retain already-decoded keys.
pub trait KeyCache {
    /// Borrow a cached key, or `None` if it is absent. Implementations may
    /// update hit counters or recency state through interior mutability.
    fn get(&self, encoded: &[u8; 32]) -> Option<&CachedPublicKey>;

    /// Borrow one SIMD chunk of cached keys.
    fn get_batch<'a>(
        &'a self,
        keys: &[[u8; 32]; SIMD_LANES],
    ) -> [Option<&'a CachedPublicKey>; SIMD_LANES] {
        core::array::from_fn(|lane| self.get(&keys[lane]))
    }

    /// Optionally retain an already-decoded key for later chunks or batches.
    /// The default implementation leaves the cache unchanged.
    fn insert(&mut self, _key: CachedPublicKey) {}

    /// Optionally retain already-decoded keys from one SIMD chunk.
    ///
    /// Only lanes with the corresponding `insert_lanes` entry set are inserted.
    fn insert_batch(
        &mut self,
        keys: [CachedPublicKey; SIMD_LANES],
        insert_lanes: [bool; SIMD_LANES],
    ) {
        for (lane, key) in keys.into_iter().enumerate() {
            if insert_lanes[lane] {
                self.insert(key);
            }
        }
    }
}

/// A [`KeyCache`] that retains no decoded keys.
#[derive(Clone, Copy, Debug, Default)]
pub struct NullKeyCache;

impl NullKeyCache {
    pub fn new() -> Self {
        Self
    }
}

impl KeyCache for NullKeyCache {
    #[inline]
    fn get(&self, _encoded: &[u8; 32]) -> Option<&CachedPublicKey> {
        None
    }
}
