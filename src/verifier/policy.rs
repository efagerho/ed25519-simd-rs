use super::driver::{verify_cached_batch_for, verify_uncached_batch_for};
use super::{R_ENCODING_LEN, SIMD_LANES, Verifier};
use crate::batch::PendingLanes;
use crate::cache::NullKeyCache;
use crate::edwards::{BasepointTableEntries, PointTable};
use crate::hot_key_cache::HotKeyCache;
use crate::input::{PUBLIC_KEY_LEN, VerifyInput};
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

/// The Ed25519 field modulus `p = 2^255 - 19`, encoded little-endian.
const FIELD_P_BYTES: [u8; 32] = [
    0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
];

pub(crate) fn r_encoding_has_canonical_y(r_bytes: &[u8; R_ENCODING_LEN]) -> bool {
    let mut y = *r_bytes;
    y[31] &= 0x7f;
    let mut i = 32;
    while i > 0 {
        i -= 1;
        if y[i] < FIELD_P_BYTES[i] {
            return true;
        }
        if y[i] > FIELD_P_BYTES[i] {
            return false;
        }
    }
    false
}

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
pub struct DalekQueues {
    dalek_candidates: Vec<avx512ifma::DalekCandidate>,
    dalek_r_bytes: Vec<[[u8; R_ENCODING_LEN]; SIMD_LANES]>,
    dalek_pending: Vec<PendingLanes>,
}

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
/// `WideRPoint`, and `PreparedChunk` into the public API.
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
    fn decode_keys_and_r(
        keys: &[[u8; PUBLIC_KEY_LEN]; SIMD_LANES],
        r_bytes: &[[u8; R_ENCODING_LEN]; SIMD_LANES],
        key_tables: &mut [Option<PointTable>; SIMD_LANES],
    ) -> (u8, avx512ifma::WideRPoint, u8);

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
    fn decode_keys_and_r(
        keys: &[[u8; PUBLIC_KEY_LEN]; SIMD_LANES],
        r_bytes: &[[u8; R_ENCODING_LEN]; SIMD_LANES],
        key_tables: &mut [Option<PointTable>; SIMD_LANES],
    ) -> (u8, avx512ifma::WideRPoint, u8) {
        avx512ifma::decode_keys_and_decompress_r::<false>(keys, r_bytes, key_tables)
    }

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
        avx512ifma::zip215::check_decoded(chunk, base, r, r_valid, lanes, out);
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
    fn decode_keys_and_r(
        keys: &[[u8; PUBLIC_KEY_LEN]; SIMD_LANES],
        r_bytes: &[[u8; R_ENCODING_LEN]; SIMD_LANES],
        key_tables: &mut [Option<PointTable>; SIMD_LANES],
    ) -> (u8, avx512ifma::WideRPoint, u8) {
        avx512ifma::decode_keys_and_decompress_r::<true>(keys, r_bytes, key_tables)
    }

    #[inline(always)]
    fn reject_small_order_keys(
        public_key_tables: &[&PointTable; SIMD_LANES],
        valid: &mut [bool; SIMD_LANES],
    ) {
        let small_order = avx512ifma::public_key_small_order_lanes(public_key_tables);
        for lane in 0..SIMD_LANES {
            valid[lane] &= !small_order[lane];
        }
    }

    #[inline(always)]
    fn verify_encoded(
        chunk: &HashedChunk<'_>,
        base: &BasepointTableEntries,
        lanes: PendingLanes,
        queues: &mut Self::Queues,
        out: &mut [bool],
    ) {
        let candidate = chunk.with_digits(|p| avx512ifma::prepare_dalek_candidate(p, base));
        queues.dalek_candidates.push(candidate);
        queues.dalek_r_bytes.push(*chunk.r_bytes);
        queues.dalek_pending.push(lanes);
        if queues.dalek_candidates.len() == avx512ifma::DALEK_BATCH {
            flush_dalek_queue(queues, out);
        }
    }

    fn verify_decoded(
        chunk: &HashedChunk<'_>,
        base: &BasepointTableEntries,
        r: &avx512ifma::WideRPoint,
        r_valid: u8,
        lanes: &PendingLanes,
        out: &mut [bool],
    ) {
        let equation =
            chunk.with_digits(|p| avx512ifma::verify_prepared_dalek_decompressed_r(p, r, base));
        let x_zero = r.x_zero_lanes();
        let small_order = r.small_order_lanes();
        lanes.score(out, |j| {
            let bytes = &chunk.r_bytes[j];
            let signed_zero = x_zero[j] && bytes[31] & 0x80 != 0;
            equation[j]
                && r_valid & (1 << j) != 0
                && r_encoding_has_canonical_y(bytes)
                && !signed_zero
                && !small_order[j]
        });
    }

    fn flush_queue(queues: &mut Self::Queues, out: &mut [bool]) {
        flush_dalek_queue(queues, out);
    }
}

/// Recompress the queued candidates and scatter accepted lanes to the caller.
fn flush_dalek_queue(queues: &mut DalekQueues, out: &mut [bool]) {
    let DalekQueues {
        dalek_candidates: candidates,
        dalek_r_bytes: r_bytes,
        dalek_pending: pending,
    } = queues;
    if candidates.is_empty() {
        return;
    }
    debug_assert_eq!(candidates.len(), pending.len());
    let masks = avx512ifma::check_dalek_candidates(candidates, r_bytes);
    for (chunk, mask) in pending.drain(..).zip(masks) {
        chunk.score(out, |lane| mask & (1 << lane) != 0);
    }
    candidates.clear();
    r_bytes.clear();
}
