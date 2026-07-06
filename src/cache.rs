use crate::batch::PUBLIC_KEY_LEN;
use crate::edwards::{EdwardsPoint, PointTable};

pub(crate) mod private {
    pub trait Sealed {}
}

/// A decoded public key and its precomputed multiplication table.
#[derive(Clone, Debug)]
pub struct CachedPublicKey {
    pub(crate) encoded: [u8; PUBLIC_KEY_LEN],
    pub(crate) table: PointTable,
}

impl CachedPublicKey {
    /// Build a cached public key from its encoded bytes.
    pub fn from_encoded(encoded: [u8; PUBLIC_KEY_LEN]) -> Option<Self> {
        EdwardsPoint::decompress(&encoded).map(|point| Self {
            encoded,
            table: PointTable::new(&point),
        })
    }

    /// Return the encoded public key bytes this was built from.
    pub fn encoded(&self) -> [u8; PUBLIC_KEY_LEN] {
        self.encoded
    }
}

/// Storage policy for decoded public keys.
///
/// [`NullKeyCache`] retains no decoded keys and is the verifier default.
/// [`HotKeyCache`](crate::HotKeyCache) retains keys across batches for workloads
/// with repeated hot keys. Decoding is owned by the verifier; caches only look
/// up and retain already-decoded keys.
pub trait KeyCache: private::Sealed {
    /// Borrow a cached key, or `None` if it is absent. Implementations may
    /// update hit counters or recency state through interior mutability.
    fn get(&self, encoded: &[u8; PUBLIC_KEY_LEN]) -> Option<&CachedPublicKey>;

    /// Optionally retain an already-decoded key for later chunks or batches.
    /// The default implementation leaves the cache unchanged.
    fn insert(&mut self, _key: CachedPublicKey) {}
}

/// A [`KeyCache`] that retains no decoded keys.
#[derive(Clone, Copy, Debug, Default)]
pub struct NullKeyCache;

impl NullKeyCache {
    pub fn new() -> Self {
        Self
    }
}

impl private::Sealed for NullKeyCache {}

impl KeyCache for NullKeyCache {
    #[inline]
    fn get(&self, _encoded: &[u8; PUBLIC_KEY_LEN]) -> Option<&CachedPublicKey> {
        None
    }
}
