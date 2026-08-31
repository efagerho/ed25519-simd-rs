mod driver;
mod policy;

use crate::batch;
use crate::cache::{KeyCache, NullKeyCache};
use crate::edwards::{BasepointTable, BasepointTableEntries, PointTable};
use crate::input::VerifyInput;
use driver::ChunkScratch;
use std::sync::LazyLock;

pub use policy::{DalekPolicy, VerificationPolicy, VerifyPolicy, Zip215Policy};

const SIMD_LANES: usize = batch::SIMD_LANES;
const R_ENCODING_LEN: usize = batch::R_ENCODING_LEN;

// Shared once per process; the base-point table is policy- and cache-independent.
static BASE_TABLE: LazyLock<BasepointTable> = LazyLock::new(BasepointTable::new);

// Placeholder table for invalid/missing lanes, also shared across verifiers.
static IDENTITY_TABLE: LazyLock<PointTable> = LazyLock::new(PointTable::cold_identity);

/// Batch Ed25519 verifier for a compile-time [`VerificationPolicy`] and [`KeyCache`].
/// Reuse one across [`verify_batch`](Verifier::verify_batch) calls.
#[derive(Debug)]
pub struct Verifier<P: VerificationPolicy = Zip215Policy, C: KeyCache = NullKeyCache> {
    policy: core::marker::PhantomData<P>,
    base_table: &'static BasepointTableEntries,
    // Invalid lanes are masked out but still need a real ladder table.
    identity_table: &'static PointTable,
    visit_order: Vec<usize>,
    queues: C::Queues<P>,
    scratch: Box<ChunkScratch>,
    cache: C,
}

/// A verifier fixed to ZIP-215 at compile time.
pub type Zip215Verifier<C = NullKeyCache> = Verifier<Zip215Policy, C>;

/// A verifier fixed to Dalek-compatible rules at compile time.
pub type DalekVerifier<C = NullKeyCache> = Verifier<DalekPolicy, C>;

/// Explicit runtime choice between the two monomorphized verifier types.
///
/// Prefer [`Zip215Verifier`] or [`DalekVerifier`] when the policy is known at
/// compile time. This wrapper intentionally includes both code paths.
#[derive(Debug)]
pub enum RuntimeVerifier<C: KeyCache = NullKeyCache> {
    /// ZIP-215 verifier.
    Zip215(Zip215Verifier<C>),
    /// Dalek-compatible verifier.
    Dalek(DalekVerifier<C>),
}

impl<P: VerificationPolicy> Default for Verifier<P, NullKeyCache> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: VerificationPolicy> Verifier<P, NullKeyCache> {
    /// Create a verifier with its type-selected policy and no retained-key cache.
    pub fn new() -> Self {
        Self::with_cache(NullKeyCache::new())
    }
}

impl<P: VerificationPolicy, C: KeyCache> Verifier<P, C> {
    /// Create a verifier backed by a caller-provided cache.
    pub fn with_cache(cache: C) -> Self {
        Self {
            policy: core::marker::PhantomData,
            base_table: BASE_TABLE.entries(),
            identity_table: &*IDENTITY_TABLE,
            visit_order: Vec::new(),
            queues: C::Queues::<P>::default(),
            scratch: Box::new(ChunkScratch::new()),
            cache,
        }
    }

    /// Borrow the configured cache.
    pub fn cache(&self) -> &C {
        &self.cache
    }

    /// Mutably borrow the configured cache.
    pub fn cache_mut(&mut self) -> &mut C {
        &mut self.cache
    }

    /// Return the verifier policy.
    pub fn policy(&self) -> VerifyPolicy {
        P::POLICY
    }

    /// Verify a batch and write one boolean result per input. `out[i]` is
    /// `true` iff `inputs[i]`'s signature is valid for its `(public_key, message)`.
    ///
    /// # Panics
    ///
    /// Panics if `inputs.len() != out.len()`.
    pub fn verify_batch(&mut self, inputs: &[VerifyInput<'_>], out: &mut [bool]) {
        C::dispatch_verify_batch(self, inputs, out);
    }
}

impl Default for RuntimeVerifier<NullKeyCache> {
    fn default() -> Self {
        Self::new()
    }
}

impl RuntimeVerifier<NullKeyCache> {
    /// Create a ZIP-215 runtime verifier with no retained-key cache.
    pub fn new() -> Self {
        Self::with_policy(VerifyPolicy::default())
    }

    /// Create a runtime-selected verifier with no retained-key cache.
    pub fn with_policy(policy: VerifyPolicy) -> Self {
        Self::with_cache(policy, NullKeyCache::new())
    }
}

impl<C: KeyCache> RuntimeVerifier<C> {
    /// Create an explicitly runtime-selected verifier backed by `cache`.
    pub fn with_cache(policy: VerifyPolicy, cache: C) -> Self {
        match policy {
            VerifyPolicy::Zip215 => Self::Zip215(Zip215Verifier::with_cache(cache)),
            VerifyPolicy::Dalek => Self::Dalek(DalekVerifier::with_cache(cache)),
        }
    }

    /// Borrow the configured cache.
    pub fn cache(&self) -> &C {
        match self {
            Self::Zip215(verifier) => verifier.cache(),
            Self::Dalek(verifier) => verifier.cache(),
        }
    }

    /// Mutably borrow the configured cache.
    pub fn cache_mut(&mut self) -> &mut C {
        match self {
            Self::Zip215(verifier) => verifier.cache_mut(),
            Self::Dalek(verifier) => verifier.cache_mut(),
        }
    }

    /// Return the selected policy.
    pub fn policy(&self) -> VerifyPolicy {
        match self {
            Self::Zip215(_) => VerifyPolicy::Zip215,
            Self::Dalek(_) => VerifyPolicy::Dalek,
        }
    }

    /// Verify a batch with the selected policy.
    pub fn verify_batch(&mut self, inputs: &[VerifyInput<'_>], out: &mut [bool]) {
        match self {
            Self::Zip215(verifier) => verifier.verify_batch(inputs, out),
            Self::Dalek(verifier) => verifier.verify_batch(inputs, out),
        }
    }
}
