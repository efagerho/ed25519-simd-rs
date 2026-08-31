use crate::edwards::PointTable;
use crate::input::{PUBLIC_KEY_LEN, VerifyInput};
use crate::verifier::{VerificationPolicy, Verifier};
use crate::wide::avx512ifma;

pub(crate) mod private {
    /// Prevents downstream crates from implementing sealed cache policies.
    pub trait Sealed {}
}

/// A decoded public key and its precomputed multiplication table.
///
/// A later signature from the same key can start its scalar
/// ladder with these cached multiples instead of rebuilding them.
#[derive(Clone, Debug)]
pub struct CachedPublicKey {
    pub(crate) encoded: [u8; PUBLIC_KEY_LEN],
    pub(crate) table: PointTable,
}

impl CachedPublicKey {
    /// Build a cached public key from its encoded bytes.
    pub fn from_encoded(encoded: [u8; PUBLIC_KEY_LEN]) -> Option<Self> {
        avx512ifma::decode_public_key_table(&encoded).map(|table| Self { encoded, table })
    }
}

/// Storage policy for verifier-decoded public keys.
///
/// [`NullKeyCache`] retains nothing; [`HotKeyCache`](crate::HotKeyCache)
/// retains repeated keys across batches. This trait is sealed; downstream
/// crates can select a provided policy but cannot implement their own.
pub trait KeyCache: private::Sealed {
    /// Policy/cache-specific reusable verification state.
    #[doc(hidden)]
    type Queues<P: VerificationPolicy>: core::fmt::Debug + Default;

    /// Borrow a cached key, or `None` if it is absent. Implementations may
    /// update recency state through interior mutability.
    fn get(&self, encoded: &[u8; PUBLIC_KEY_LEN]) -> Option<&CachedPublicKey>;

    /// Optionally retain an already-decoded key for later chunks or batches.
    /// The default implementation leaves the cache unchanged.
    fn insert(&mut self, _key: CachedPublicKey) {}

    /// Dispatch into a cache-capability-specific batch driver.
    #[doc(hidden)]
    fn dispatch_verify_batch<P: VerificationPolicy>(
        verifier: &mut Verifier<P, Self>,
        inputs: &[VerifyInput<'_>],
        out: &mut [bool],
    ) where
        Self: Sized;
}

/// Zero-sized verification state for a cache that cannot hit.
#[doc(hidden)]
#[derive(Debug, Default)]
pub struct NoQueues;

/// A [`KeyCache`] that retains no decoded keys.
#[derive(Clone, Copy, Debug, Default)]
pub struct NullKeyCache;

impl NullKeyCache {
    /// Create the no-op cache.
    pub fn new() -> Self {
        Self
    }
}

impl private::Sealed for NullKeyCache {}

impl KeyCache for NullKeyCache {
    type Queues<P: VerificationPolicy> = NoQueues;

    #[inline]
    fn get(&self, _encoded: &[u8; PUBLIC_KEY_LEN]) -> Option<&CachedPublicKey> {
        None
    }

    #[inline]
    fn dispatch_verify_batch<P: VerificationPolicy>(
        verifier: &mut Verifier<P, Self>,
        inputs: &[VerifyInput<'_>],
        out: &mut [bool],
    ) {
        P::dispatch_uncached_verify_batch(verifier, inputs, out);
    }
}
