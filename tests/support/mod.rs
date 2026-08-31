#![allow(dead_code)]

use core::convert::TryFrom;

use curve25519::ed_sigs::{Signature, SigningKey, VerificationKey, VerificationKeyBytes};
use ed25519_simd::{
    HotKeyCache, NullKeyCache, PUBLIC_KEY_LEN, RuntimeVerifier, SIGNATURE_LEN, VerifyInput,
    VerifyPolicy,
};

pub fn hex_vec(s: &str) -> Vec<u8> {
    hex::decode(s).expect("valid test vector hex")
}

pub fn hex_array<const N: usize>(s: &str) -> [u8; N] {
    let mut out = [0u8; N];
    hex::decode_to_slice(s, &mut out).expect("valid fixed-length test vector hex");
    out
}

pub fn verify(policy: VerifyPolicy, input: VerifyInput<'_>) -> bool {
    let mut verifier = RuntimeVerifier::with_cache(policy, NullKeyCache::new());
    let mut out = [false];
    verifier.verify_batch(&[input], &mut out);
    out[0]
}

/// Verify twice and return the warm-cache result, exercising Dalek's byte
/// comparison instead of its cold-cache projective comparison.
pub fn verify_warm(policy: VerifyPolicy, input: VerifyInput<'_>) -> bool {
    let mut verifier = RuntimeVerifier::with_cache(policy, HotKeyCache::with_capacity(8));
    let mut out = [false];
    verifier.verify_batch(&[input], &mut out);
    verifier.verify_batch(&[input], &mut out);
    out[0]
}

pub fn verify_batch(policy: VerifyPolicy, inputs: &[VerifyInput<'_>]) -> Vec<bool> {
    let mut verifier = RuntimeVerifier::with_cache(policy, NullKeyCache::new());
    let mut out = vec![false; inputs.len()];
    verifier.verify_batch(inputs, &mut out);
    out
}

pub fn solana_ed25519_verify_zebra(
    public_key: [u8; PUBLIC_KEY_LEN],
    signature: [u8; SIGNATURE_LEN],
    message: &[u8],
) -> bool {
    let vk_bytes = VerificationKeyBytes::from(public_key);
    let sig = Signature::from(signature);
    VerificationKey::try_from(vk_bytes)
        .and_then(|vk| vk.verify_zebra(&sig, message))
        .is_ok()
}

pub fn solana_ed25519_verify_dalek(
    public_key: [u8; PUBLIC_KEY_LEN],
    signature: [u8; SIGNATURE_LEN],
    message: &[u8],
) -> bool {
    let vk_bytes = VerificationKeyBytes::from(public_key);
    let sig = Signature::from(signature);
    VerificationKey::try_from(vk_bytes)
        .and_then(|vk| vk.verify_dalek(&sig, message))
        .is_ok()
}

pub fn signing_key_from_index(index: u64) -> SigningKey {
    let mut seed = [0u8; 32];
    seed[..8].copy_from_slice(&index.to_le_bytes());
    SigningKey::from(seed)
}

/// Owned verification input used by integration-test generators.
#[derive(Clone)]
pub struct Case {
    pub public_key: [u8; PUBLIC_KEY_LEN],
    pub signature: [u8; SIGNATURE_LEN],
    pub message: Vec<u8>,
}

impl Case {
    pub fn input(&self) -> VerifyInput<'_> {
        VerifyInput {
            public_key: self.public_key,
            signature: self.signature,
            message: &self.message,
        }
    }
}
