use super::driver::{verify_cached_batch_for, verify_uncached_batch_for};
use super::{R_ENCODING_LEN, SIMD_LANES, Verifier};
use crate::cache::{KeyCache, NullKeyCache};
use crate::edwards::PointTable;
use crate::hot_key_cache::HotKeyCache;
use crate::input::{PUBLIC_KEY_LEN, VerifyInput};
use crate::wide::{PreparedChunk, avx512ifma};

/// Which acceptance rules a [`Verifier`](crate::Verifier) applies.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum VerifyPolicy {
    /// ZIP-215 cofactored verification; accepts non-canonical point encodings.
    #[default]
    Zip215,
    /// Dalek-style canonical-`R` verification with solana-ed25519 legacy filters.
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

/// solana-ed25519's legacy `R` blacklist, kept byte-for-byte for Dalek policy
/// compatibility.
const LEGACY_EXCLUDED_R_ENCODINGS: [[u8; R_ENCODING_LEN]; 11] = [
    // Canonical encoding of a y=0 order-4 point.
    [0x00; R_ENCODING_LEN],
    // Canonical identity encoding: y=1, x=0.
    {
        let mut e = [0x00; R_ENCODING_LEN];
        e[0] = 0x01;
        e
    },
    // Canonical encoding of an order-8 point.
    [
        0x26, 0xe8, 0x95, 0x8f, 0xc2, 0xb2, 0x27, 0xb0, 0x45, 0xc3, 0xf4, 0x89, 0xf2, 0xef, 0x98,
        0xf0, 0xd5, 0xdf, 0xac, 0x05, 0xd3, 0xc6, 0x33, 0x39, 0xb1, 0x38, 0x02, 0x88, 0x6d, 0x53,
        0xfc, 0x05,
    ],
    // Canonical encoding of an order-8 point.
    [
        0xc7, 0x17, 0x6a, 0x70, 0x3d, 0x4d, 0xd8, 0x4f, 0xba, 0x3c, 0x0b, 0x76, 0x0d, 0x10, 0x67,
        0x0f, 0x2a, 0x20, 0x53, 0xfa, 0x2c, 0x39, 0xcc, 0xc6, 0x4e, 0xc7, 0xfd, 0x77, 0x92, 0xac,
        0x03, 0x7a,
    ],
    // Valid canonical encoding of a non-small-order point included by the legacy blacklist.
    [
        0x13, 0xe8, 0x95, 0x8f, 0xc2, 0xb2, 0x27, 0xb0, 0x45, 0xc3, 0xf4, 0x89, 0xf2, 0xef, 0x98,
        0xf0, 0xd5, 0xdf, 0xac, 0x05, 0xd3, 0xc6, 0x33, 0x39, 0xb1, 0x38, 0x02, 0x88, 0x6d, 0x53,
        0xfc, 0x85,
    ],
    // Invalid encoding; it does not decompress to an Edwards point.
    [
        0xb4, 0x17, 0x6a, 0x70, 0x3d, 0x4d, 0xd8, 0x4f, 0xba, 0x3c, 0x0b, 0x76, 0x0d, 0x10, 0x67,
        0x0f, 0x2a, 0x20, 0x53, 0xfa, 0x2c, 0x39, 0xcc, 0xc6, 0x4e, 0xc7, 0xfd, 0x77, 0x92, 0xac,
        0x03, 0xfa,
    ],
    // Canonical encoding of the order-2 point: y=-1, x=0.
    [
        0xec, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0x7f,
    ],
    // Non-canonical y=p encoding of the same y=0 order-4 point as entry 0.
    [
        0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0x7f,
    ],
    // Non-canonical y=p+1 encoding of the identity point.
    [
        0xee, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0x7f,
    ],
    // Invalid encoding; y=p-20 with the x sign bit set is not on the curve.
    [
        0xd9, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff,
    ],
    // Valid canonical encoding of a non-small-order point included by the legacy blacklist.
    [
        0xda, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff,
    ],
];

/// The Ed25519 field modulus `p = 2^255 - 19`, encoded little-endian.
const FIELD_P_BYTES: [u8; 32] = [
    0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
];

pub(crate) fn r_encoding_is_legacy_excluded(r_bytes: &[u8; R_ENCODING_LEN]) -> bool {
    LEGACY_EXCLUDED_R_ENCODINGS.contains(r_bytes)
}

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

/// Per-lane output bookkeeping shared by the policy-specific pending records.
#[derive(Debug)]
pub(super) struct PendingLanes {
    pub(super) valid: [bool; SIMD_LANES],
    pub(super) output_indices: [usize; SIMD_LANES],
    pub(super) active_lane_count: usize,
}

/// Dalek additionally needs both original encodings after recompression.
#[derive(Debug)]
struct PendingDalekChunk {
    lanes: PendingLanes,
    r_bytes: [[u8; R_ENCODING_LEN]; SIMD_LANES],
    public_keys: [[u8; PUBLIC_KEY_LEN]; SIMD_LANES],
}

/// Reusable ZIP-215-only buffers.
///
/// Two queued candidates let their `R` inverse-square-root chains
/// alternate IFMA operations, hiding each chain's multiplication latency.
#[doc(hidden)]
#[derive(Debug, Default)]
pub struct Zip215Queues {
    zip215_candidates: Vec<avx512ifma::Zip215Candidate>,
    zip215_r_bytes: Vec<[[u8; R_ENCODING_LEN]; SIMD_LANES]>,
    zip215_pending: Vec<PendingLanes>,
}

/// Reusable Dalek-only buffers.
///
/// Eight queued projective candidates share one Montgomery batch
/// inversion before their affine encodings are compared with the signatures.
#[doc(hidden)]
#[derive(Debug, Default)]
pub struct DalekQueues {
    dalek_candidates: Vec<avx512ifma::DalekCandidate>,
    dalek_pending: Vec<PendingDalekChunk>,
}

/// The per-lane chunk data both policies score their SIMD result against.
pub(super) struct ScoredLanes<'a> {
    pub(super) r_bytes: &'a [[u8; R_ENCODING_LEN]; SIMD_LANES],
    pub(super) public_keys: &'a [[u8; PUBLIC_KEY_LEN]; SIMD_LANES],
    pub(super) valid: &'a [bool; SIMD_LANES],
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

    fn verify_lanes<C: KeyCache>(
        verifier: &Verifier<Self, C>,
        prepared: &PreparedChunk<'_>,
        decoded_r: Option<(avx512ifma::WideRPoint, [bool; SIMD_LANES])>,
        lanes: &ScoredLanes<'_>,
        out: &mut [bool; SIMD_LANES],
        queues: &mut Self::Queues,
    ) -> bool;

    fn push_pending(
        queues: &mut Self::Queues,
        lanes: PendingLanes,
        r_bytes: [[u8; R_ENCODING_LEN]; SIMD_LANES],
        public_keys: [[u8; PUBLIC_KEY_LEN]; SIMD_LANES],
    );

    fn queue_is_full(queues: &Self::Queues) -> bool;
    fn flush_queue(queues: &mut Self::Queues, out: &mut [bool]);
}

/// Policy operations specialized for batches that cannot contain cache hits.
pub(super) trait UncachedPolicyOps: PolicyOps {
    fn verify_decoded_lanes(
        verifier: &Verifier<Self, NullKeyCache>,
        prepared: &PreparedChunk<'_>,
        r_points: &avx512ifma::WideRPoint,
        r_valid_lanes: &[bool; SIMD_LANES],
        lanes: &ScoredLanes<'_>,
        out: &mut [bool; SIMD_LANES],
    );
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
    fn verify_lanes<C: KeyCache>(
        verifier: &Verifier<Self, C>,
        prepared: &PreparedChunk<'_>,
        decoded_r: Option<(avx512ifma::WideRPoint, [bool; SIMD_LANES])>,
        lanes: &ScoredLanes<'_>,
        out: &mut [bool; SIMD_LANES],
        queues: &mut Self::Queues,
    ) -> bool {
        verifier.verify_zip215_lanes(
            prepared,
            decoded_r,
            lanes,
            out,
            &mut queues.zip215_candidates,
        )
    }

    #[inline(always)]
    fn push_pending(
        queues: &mut Self::Queues,
        lanes: PendingLanes,
        r_bytes: [[u8; R_ENCODING_LEN]; SIMD_LANES],
        _public_keys: [[u8; PUBLIC_KEY_LEN]; SIMD_LANES],
    ) {
        queues.zip215_r_bytes.push(r_bytes);
        queues.zip215_pending.push(lanes);
    }

    #[inline(always)]
    fn queue_is_full(queues: &Self::Queues) -> bool {
        queues.zip215_candidates.len() == avx512ifma::ZIP215_BATCH
    }

    #[inline(always)]
    fn flush_queue(queues: &mut Self::Queues, out: &mut [bool]) {
        flush_zip215_queue(queues, out);
    }
}

impl UncachedPolicyOps for Zip215Policy {
    #[inline(always)]
    fn verify_decoded_lanes(
        verifier: &Verifier<Self, NullKeyCache>,
        prepared: &PreparedChunk<'_>,
        r_points: &avx512ifma::WideRPoint,
        r_valid_lanes: &[bool; SIMD_LANES],
        lanes: &ScoredLanes<'_>,
        out: &mut [bool; SIMD_LANES],
    ) {
        let equation_holds =
            avx512ifma::verify_prepared_zip215(prepared, r_points, verifier.base_table);
        score_zip215_lanes(&equation_holds, r_valid_lanes, lanes, out);
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
    fn verify_lanes<C: KeyCache>(
        verifier: &Verifier<Self, C>,
        prepared: &PreparedChunk<'_>,
        decoded_r: Option<(avx512ifma::WideRPoint, [bool; SIMD_LANES])>,
        lanes: &ScoredLanes<'_>,
        out: &mut [bool; SIMD_LANES],
        queues: &mut Self::Queues,
    ) -> bool {
        verifier.verify_dalek_lanes(
            prepared,
            decoded_r,
            lanes,
            out,
            &mut queues.dalek_candidates,
        )
    }

    #[inline(always)]
    fn push_pending(
        queues: &mut Self::Queues,
        lanes: PendingLanes,
        r_bytes: [[u8; R_ENCODING_LEN]; SIMD_LANES],
        public_keys: [[u8; PUBLIC_KEY_LEN]; SIMD_LANES],
    ) {
        queues.dalek_pending.push(PendingDalekChunk {
            lanes,
            r_bytes,
            public_keys,
        });
    }

    #[inline(always)]
    fn queue_is_full(queues: &Self::Queues) -> bool {
        queues.dalek_candidates.len() == avx512ifma::DALEK_BATCH
    }

    #[inline(always)]
    fn flush_queue(queues: &mut Self::Queues, out: &mut [bool]) {
        flush_dalek_queue(queues, out);
    }
}

impl UncachedPolicyOps for DalekPolicy {
    #[inline(always)]
    fn verify_decoded_lanes(
        verifier: &Verifier<Self, NullKeyCache>,
        prepared: &PreparedChunk<'_>,
        r_points: &avx512ifma::WideRPoint,
        r_valid_lanes: &[bool; SIMD_LANES],
        lanes: &ScoredLanes<'_>,
        out: &mut [bool; SIMD_LANES],
    ) {
        let equation_holds = avx512ifma::verify_prepared_dalek_decompressed_r(
            prepared,
            r_points,
            verifier.base_table,
        );
        score_dalek_lanes(&equation_holds, r_points, r_valid_lanes, lanes, out);
    }
}

/// Score one chunk's lanes against an already-decompressed `R` under ZIP-215.
///
/// The sole home of the ZIP-215 accept predicate: both the cached and the
/// cache-free driver route here so the two cannot drift apart.
#[inline(always)]
pub(super) fn score_zip215_lanes(
    equation_holds: &[bool; SIMD_LANES],
    r_valid_lanes: &[bool; SIMD_LANES],
    lanes: &ScoredLanes<'_>,
    out: &mut [bool; SIMD_LANES],
) {
    for lane in 0..SIMD_LANES {
        out[lane] =
            zip215_lane_accepts(equation_holds[lane], lanes.valid[lane], r_valid_lanes[lane]);
    }
}

#[inline(always)]
fn zip215_lane_accepts(equation_holds: bool, input_valid: bool, r_valid: bool) -> bool {
    equation_holds && input_valid && r_valid
}

/// Score one chunk's lanes against an already-decompressed `R` under the Dalek
/// rules: canonical `y`, no negative zero, and the legacy `R` blacklist.
///
/// The sole home of the Dalek accept predicate; see [`score_zip215_lanes`].
#[inline(always)]
pub(super) fn score_dalek_lanes(
    equation_holds: &[bool; SIMD_LANES],
    r_points: &avx512ifma::WideRPoint,
    r_valid_lanes: &[bool; SIMD_LANES],
    lanes: &ScoredLanes<'_>,
    out: &mut [bool; SIMD_LANES],
) {
    let r_x_zero = r_points.x_zero_lanes();
    for lane in 0..SIMD_LANES {
        let r_bytes = &lanes.r_bytes[lane];
        let signed_zero = r_x_zero[lane] && r_bytes[31] & 0x80 != 0;
        out[lane] = equation_holds[lane]
            && lanes.valid[lane]
            && r_valid_lanes[lane]
            && r_encoding_has_canonical_y(r_bytes)
            && !signed_zero
            && !dalek_legacy_excluded(&lanes.public_keys[lane], r_bytes);
    }
}

/// Compress every queued candidate through one shared inversion and score the
/// chunks against their encoded `R`. Leaves both queues empty.
fn flush_dalek_queue(queues: &mut DalekQueues, out: &mut [bool]) {
    let DalekQueues {
        dalek_candidates: candidates,
        dalek_pending: pending,
    } = queues;
    if candidates.is_empty() {
        return;
    }
    debug_assert_eq!(candidates.len(), pending.len());

    let mut encodings = [[[0u8; R_ENCODING_LEN]; SIMD_LANES]; avx512ifma::DALEK_BATCH];
    avx512ifma::compress_dalek_candidates(candidates, &mut encodings[..candidates.len()]);

    for (chunk, encoding) in pending.drain(..).zip(&encodings) {
        for lane in 0..chunk.lanes.active_lane_count {
            // Recompression is canonical, so a non-canonical or wrong-sign `R`
            // encoding simply fails to match; only the legacy filter is extra.
            out[chunk.lanes.output_indices[lane]] = encoding[lane] == chunk.r_bytes[lane]
                && chunk.lanes.valid[lane]
                && !dalek_legacy_excluded(&chunk.public_keys[lane], &chunk.r_bytes[lane]);
        }
    }
    candidates.clear();
}

/// Check every queued ZIP-215 chunk, decompressing the pair of `R` chunks
/// through interleaved chains. Leaves both queues empty.
fn flush_zip215_queue(queues: &mut Zip215Queues, out: &mut [bool]) {
    let Zip215Queues {
        zip215_candidates: candidates,
        zip215_r_bytes: r_bytes,
        zip215_pending: pending,
    } = queues;
    if candidates.is_empty() {
        return;
    }
    debug_assert_eq!(candidates.len(), r_bytes.len());
    debug_assert_eq!(candidates.len(), pending.len());

    let checks = avx512ifma::check_zip215_candidates(candidates, r_bytes);

    for (chunk, (equation_holds, r_valid_lanes)) in pending.drain(..).zip(&checks) {
        for lane in 0..chunk.active_lane_count {
            out[chunk.output_indices[lane]] =
                zip215_lane_accepts(equation_holds[lane], chunk.valid[lane], r_valid_lanes[lane]);
        }
    }
    candidates.clear();
    r_bytes.clear();
}

fn dalek_legacy_excluded(
    public_key: &[u8; PUBLIC_KEY_LEN],
    r_bytes: &[u8; R_ENCODING_LEN],
) -> bool {
    *public_key == [0u8; PUBLIC_KEY_LEN] || r_encoding_is_legacy_excluded(r_bytes)
}
