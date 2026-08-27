//! Deterministic pseudo-random test data.
//!
//! The unit tests need a lot of arbitrary field elements, scalars and cache
//! keys, and they need the same ones on every run so a failure reproduces from
//! the seed printed in the assertion. This is a plain LCG rather than anything
//! statistically serious: it only has to spread values across the input space.

/// Multiplier from Steele & Vigna's survey of LCG constants for 64-bit state.
const MULTIPLIER: u64 = 0xd134_2543_de82_ef95;
const INCREMENT: u64 = 0x9e37_79b9_7f4a_7c15;

pub(crate) struct TestRng(u64);

impl TestRng {
    /// Seed the generator. Callers pass a per-test constant so each test's
    /// sequence is independent but reproducible.
    pub(crate) fn new(seed: u64) -> Self {
        Self(seed)
    }

    pub(crate) fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(MULTIPLIER).wrapping_add(INCREMENT);
        self.0
    }

    /// Fill `bytes` with little-endian words, handling a short final chunk.
    pub(crate) fn fill(&mut self, bytes: &mut [u8]) {
        for chunk in bytes.chunks_mut(8) {
            let word = self.next_u64().to_le_bytes();
            chunk.copy_from_slice(&word[..chunk.len()]);
        }
    }
}
