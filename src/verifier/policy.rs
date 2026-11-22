use super::driver::{verify_cached_batch_for, verify_uncached_batch_for};
use super::{SIMD_LANES, Verifier};
use crate::batch::PendingLanes;
use crate::cache::NullKeyCache;
use crate::edwards::{BasepointTableEntries, PointTable};
use crate::hot_key_cache::HotKeyCache;
use crate::input::VerifyInput;
use crate::wide::{HashedChunk, avx512ifma};

/// Which acceptance rules a [`Verifier`](crate::Verifier) applies.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum VerifyPolicy {
    /// ZIP-215 cofactored verification; accepts non-canonical point encodings.
    #[default]
    Zip215,
    /// Strict Dalek-style verification with canonical `R` and no small-order points.
    Dalek,
}

/// ZIP-215 cofactored verification policy.
///
/// Use this as the policy parameter of [`Verifier`](crate::Verifier), or use
/// the [`Zip215Verifier`](crate::Zip215Verifier) alias.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Zip215Policy;

/// Dalek-compatible verification policy.
///
/// Use this as the policy parameter of [`Verifier`](crate::Verifier), or use
/// the [`DalekVerifier`](crate::DalekVerifier) alias.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct DalekPolicy;

/// Reusable storage for deferred ZIP-215 candidates, encodings and output positions.
#[doc(hidden)]
#[derive(Debug, Default)]
pub struct Zip215Queues(avx512ifma::zip215::Queue);

/// Reusable Dalek-only buffers.
///
/// Queuing up to eight chunks amortizes the field inversion in the
/// comparison with the original signature encodings.
#[doc(hidden)]
#[derive(Debug, Default)]
pub struct DalekQueues(avx512ifma::dalek::Queue);

mod sealed {
    /// Prevents downstream crates from defining verification policies.
    pub trait Sealed {}

    impl Sealed for super::Zip215Policy {}
    impl Sealed for super::DalekPolicy {}
}

/// A compile-time verification policy.
///
/// This trait is sealed; use [`Zip215Policy`] or [`DalekPolicy`]. Keeping the
/// policy in the verifier's type lets the linker discard the other policy's
/// decoding, scoring, and deferral code.
///
/// The `dispatch_*` methods below look like removable forwarding, but they are
/// what keeps the crate-private `PolicyOps` out of this public trait's
/// bounds. Making `PolicyOps` a supertrait instead fails: its `Queues`
/// associated type is projected by the public `KeyCache::Queues<P>`, so a
/// `pub(crate)` `PolicyOps` is rejected outright (`E0446`, crate-private
/// associated type in public interface) and a `pub` one leaks `PointTable`,
/// `WideRPoint`, and `HashedChunk` into the public API.
pub trait VerificationPolicy: sealed::Sealed + Copy + core::fmt::Debug + Default + 'static {
    /// Policy-specific reusable queue storage.
    #[doc(hidden)]
    type Queues: core::fmt::Debug + Default;

    /// The corresponding runtime policy value.
    const POLICY: VerifyPolicy;

    /// Dispatch into the monomorphized cached implementation.
    #[doc(hidden)]
    fn dispatch_cached_verify_batch(
        verifier: &mut Verifier<Self, HotKeyCache>,
        inputs: &[VerifyInput<'_>],
        out: &mut [bool],
    );

    /// Dispatch into the monomorphized cache-free implementation.
    #[doc(hidden)]
    fn dispatch_uncached_verify_batch(
        verifier: &mut Verifier<Self, NullKeyCache>,
        inputs: &[VerifyInput<'_>],
        out: &mut [bool],
    );
}

/// Internal operations implemented differently by each verification policy.
pub(super) trait PolicyOps: VerificationPolicy {
    fn reject_small_order_keys(
        public_key_tables: &[&PointTable; SIMD_LANES],
        valid: &mut [bool; SIMD_LANES],
    );

    fn verify_encoded(
        chunk: &HashedChunk<'_>,
        base: &BasepointTableEntries,
        lanes: PendingLanes,
        queues: &mut Self::Queues,
        out: &mut [bool],
    );
    fn verify_decoded(
        chunk: &HashedChunk<'_>,
        base: &BasepointTableEntries,
        r: &avx512ifma::WideRPoint,
        r_valid: u8,
        lanes: &PendingLanes,
        out: &mut [bool],
    );
    fn flush_queue(queues: &mut Self::Queues, out: &mut [bool]);
}

impl VerificationPolicy for Zip215Policy {
    type Queues = Zip215Queues;

    const POLICY: VerifyPolicy = VerifyPolicy::Zip215;

    #[inline]
    fn dispatch_cached_verify_batch(
        verifier: &mut Verifier<Self, HotKeyCache>,
        inputs: &[VerifyInput<'_>],
        out: &mut [bool],
    ) {
        verify_cached_batch_for(verifier, inputs, out);
    }

    #[inline]
    fn dispatch_uncached_verify_batch(
        verifier: &mut Verifier<Self, NullKeyCache>,
        inputs: &[VerifyInput<'_>],
        out: &mut [bool],
    ) {
        verify_uncached_batch_for(verifier, inputs, out);
    }
}

impl PolicyOps for Zip215Policy {
    #[inline(always)]
    fn reject_small_order_keys(
        _public_key_tables: &[&PointTable; SIMD_LANES],
        _valid: &mut [bool; SIMD_LANES],
    ) {
    }

    #[inline(always)]
    fn verify_encoded(
        chunk: &HashedChunk<'_>,
        base: &BasepointTableEntries,
        lanes: PendingLanes,
        queues: &mut Self::Queues,
        out: &mut [bool],
    ) {
        queues.0.push(chunk, base, lanes, out);
    }

    fn verify_decoded(
        chunk: &HashedChunk<'_>,
        base: &BasepointTableEntries,
        r: &avx512ifma::WideRPoint,
        r_valid: u8,
        lanes: &PendingLanes,
        out: &mut [bool],
    ) {
        avx512ifma::zip215::Queue::check_decoded(chunk, base, r, r_valid, lanes, out);
    }

    fn flush_queue(queues: &mut Self::Queues, out: &mut [bool]) {
        queues.0.flush(out);
    }
}

impl VerificationPolicy for DalekPolicy {
    type Queues = DalekQueues;

    const POLICY: VerifyPolicy = VerifyPolicy::Dalek;

    #[inline]
    fn dispatch_cached_verify_batch(
        verifier: &mut Verifier<Self, HotKeyCache>,
        inputs: &[VerifyInput<'_>],
        out: &mut [bool],
    ) {
        verify_cached_batch_for(verifier, inputs, out);
    }

    #[inline]
    fn dispatch_uncached_verify_batch(
        verifier: &mut Verifier<Self, NullKeyCache>,
        inputs: &[VerifyInput<'_>],
        out: &mut [bool],
    ) {
        verify_uncached_batch_for(verifier, inputs, out);
    }
}

impl PolicyOps for DalekPolicy {
    #[inline(always)]
    fn reject_small_order_keys(
        public_key_tables: &[&PointTable; SIMD_LANES],
        valid: &mut [bool; SIMD_LANES],
    ) {
        avx512ifma::dalek::reject_small_order_keys(public_key_tables, valid);
    }

    #[inline(always)]
    fn verify_encoded(
        chunk: &HashedChunk<'_>,
        base: &BasepointTableEntries,
        lanes: PendingLanes,
        queues: &mut Self::Queues,
        out: &mut [bool],
    ) {
        queues.0.push(chunk, base, lanes, out);
    }

    fn verify_decoded(
        chunk: &HashedChunk<'_>,
        base: &BasepointTableEntries,
        r: &avx512ifma::WideRPoint,
        r_valid: u8,
        lanes: &PendingLanes,
        out: &mut [bool],
    ) {
        avx512ifma::dalek::Queue::check_decoded(chunk, base, r, r_valid, lanes, out);
    }

    fn flush_queue(queues: &mut Self::Queues, out: &mut [bool]) {
        queues.0.flush(out);
    }
}
