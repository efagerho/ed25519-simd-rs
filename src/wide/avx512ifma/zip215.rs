//! Rust backend for the post-hash ZIP-215 check.
use super::decode::{WideRPoint, decompress_zip215};
use super::ladder_step::mul_s_base_minus_k_public;
use super::point::WidePoint;
use crate::batch::{EncodedPointChunk, PendingLanes};
use crate::edwards::BasepointTableEntries;
use crate::wide::HashedChunk;

#[derive(Default)]
pub(crate) struct Queue {
    candidates: Vec<WidePoint>,
    encodings: Vec<EncodedPointChunk>,
    lanes: Vec<PendingLanes>,
}

impl core::fmt::Debug for Queue {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Queue")
            .field("pending", &self.lanes.len())
            .finish()
    }
}

fn score(q: &WidePoint, r: &WidePoint, r_valid: u8, lanes: &PendingLanes, out: &mut [bool]) {
    let equation = q.subtract_affine_and_check_8_torsion(r);
    lanes.score(out, |j| equation[j] && r_valid & (1 << j) != 0);
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
        let q = chunk.with_digits(|p| mul_s_base_minus_k_public::<true>(base, p));
        score(&q, &r.point, r_valid, lanes, out);
    }

    pub(crate) fn push(
        &mut self,
        chunk: &HashedChunk<'_>,
        base: &BasepointTableEntries,
        lanes: PendingLanes,
        out: &mut [bool],
    ) {
        self.candidates
            .push(chunk.with_digits(|p| mul_s_base_minus_k_public::<true>(base, p)));
        self.encodings.push(*chunk.r_bytes);
        self.lanes.push(lanes);
        if self.lanes.len() == 2 {
            self.flush(out);
        }
    }

    pub(crate) fn flush(&mut self, out: &mut [bool]) {
        match self.lanes.len() {
            0 => return,
            1 => self.check::<1>(out),
            2 => self.check::<2>(out),
            _ => unreachable!("the queue holds at most two chunks"),
        }
        self.candidates.clear();
        self.encodings.clear();
        self.lanes.clear();
    }

    fn check<const N: usize>(&self, out: &mut [bool]) {
        let mut storage = core::mem::MaybeUninit::uninit();
        let (points, masks) =
            decompress_zip215::<N>(self.encodings.as_slice().try_into().unwrap(), &mut storage);
        for i in 0..N {
            score(
                &self.candidates[i],
                &points[i],
                masks[i],
                &self.lanes[i],
                out,
            );
        }
    }
}
