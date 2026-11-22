//! Rust backend for the post-hash Dalek check.
use super::LANES;
use super::decode::WideRPoint;
use super::multiscalar::{
    DALEK_BATCH, DalekCandidate, check_dalek_candidates, prepare_dalek_candidate,
    public_key_small_order_lanes, verify_prepared_dalek_decompressed_r,
};
use crate::batch::{EncodedPointChunk, PendingLanes, R_ENCODING_LEN};
use crate::edwards::{BasepointTableEntries, PointTable};
use crate::wide::HashedChunk;

/// The Ed25519 field modulus `p = 2^255 - 19`, encoded little-endian.
const FIELD_P_BYTES: [u8; 32] = [
    0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
];

fn r_encoding_has_canonical_y(r_bytes: &[u8; R_ENCODING_LEN]) -> bool {
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

#[derive(Default, Debug)]
pub(crate) struct Queue {
    candidates: Vec<DalekCandidate>,
    encodings: Vec<EncodedPointChunk>,
    pending: Vec<PendingLanes>,
}

pub(crate) fn reject_small_order_keys(tables: &[&PointTable; LANES], valid: &mut [bool; LANES]) {
    let small_order = public_key_small_order_lanes(tables);
    for lane in 0..LANES {
        valid[lane] &= !small_order[lane];
    }
}

impl Queue {
    pub(crate) fn check_decoded(
        chunk: &HashedChunk<'_>,
        base: &BasepointTableEntries,
        r: &WideRPoint,
        r_valid: u8,
        lanes: &PendingLanes,
        out: &mut [bool],
    ) {
        let equation = chunk.with_digits(|p| verify_prepared_dalek_decompressed_r(p, r, base));
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

    pub(crate) fn push(
        &mut self,
        chunk: &HashedChunk<'_>,
        base: &BasepointTableEntries,
        lanes: PendingLanes,
        out: &mut [bool],
    ) {
        let candidate = chunk.with_digits(|p| prepare_dalek_candidate(p, base));
        self.candidates.push(candidate);
        self.encodings.push(*chunk.r_bytes);
        self.pending.push(lanes);
        if self.candidates.len() == DALEK_BATCH {
            self.flush(out);
        }
    }

    pub(crate) fn flush(&mut self, out: &mut [bool]) {
        if self.candidates.is_empty() {
            return;
        }
        let masks = check_dalek_candidates(&self.candidates, &self.encodings);
        for (lanes, mask) in self.pending.drain(..).zip(masks) {
            lanes.score(out, |lane| mask & (1 << lane) != 0);
        }
        self.candidates.clear();
        self.encodings.clear();
    }
}
