mod driver;
mod policy;

use crate::input::VerifyInput;
use crate::wide::avx512ifma::ChunkScratch;
use core::mem::MaybeUninit;

pub use policy::{DalekPolicy, VerificationPolicy, VerifyPolicy, Zip215Policy};

/// Batch Ed25519 verifier for a compile-time [`VerificationPolicy`].
/// Reuse one across [`verify_batch`](Verifier::verify_batch) calls.
///
/// Each full chunk hashes, reduces, and evaluates eight signature
/// equations with AVX-512 while reusing scratch space for the current chunk's key tables.
#[derive(Debug)]
pub struct Verifier<P: VerificationPolicy = Zip215Policy> {
    policy: core::marker::PhantomData<P>,
    scratch: Box<MaybeUninit<ChunkScratch>>,
}

/// A verifier fixed to ZIP-215 at compile time.
pub type Zip215Verifier = Verifier<Zip215Policy>;

/// A verifier fixed to Dalek-compatible rules at compile time.
pub type DalekVerifier = Verifier<DalekPolicy>;

/// Explicit runtime choice between the two monomorphized verifier types.
///
/// Prefer [`Zip215Verifier`] or [`DalekVerifier`] when the policy is known at
/// compile time. This wrapper intentionally includes both code paths.
#[derive(Debug)]
pub enum RuntimeVerifier {
    /// ZIP-215 verifier.
    Zip215(Zip215Verifier),
    /// Dalek-compatible verifier.
    Dalek(DalekVerifier),
}

impl<P: VerificationPolicy> Default for Verifier<P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: VerificationPolicy> Verifier<P> {
    /// Create a verifier with its type-selected policy.
    pub fn new() -> Self {
        Self {
            policy: core::marker::PhantomData,
            scratch: Box::new_uninit(),
        }
    }

    /// Return the verifier policy.
    pub fn policy(&self) -> VerifyPolicy {
        P::POLICY
    }
}

impl Default for RuntimeVerifier {
    fn default() -> Self {
        Self::new()
    }
}

impl RuntimeVerifier {
    /// Create a ZIP-215 runtime verifier.
    pub fn new() -> Self {
        Self::with_policy(VerifyPolicy::default())
    }

    /// Create a runtime-selected verifier.
    pub fn with_policy(policy: VerifyPolicy) -> Self {
        match policy {
            VerifyPolicy::Zip215 => Self::Zip215(Zip215Verifier::new()),
            VerifyPolicy::Dalek => Self::Dalek(DalekVerifier::new()),
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
