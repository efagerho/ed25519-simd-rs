#![allow(dead_code)]

use core::convert::TryFrom;

use curve25519::ed_sigs::{Signature, SigningKey, VerificationKey, VerificationKeyBytes};
use ed25519_simd::{
    NullKeyCache, PUBLIC_KEY_LEN, SIGNATURE_LEN, Verifier, VerifyInput, VerifyPolicy,
};

pub fn hex_vec(s: &str) -> Vec<u8> {
    let digits: Vec<u8> = s.bytes().filter(|b| !b.is_ascii_whitespace()).collect();
    assert_eq!(digits.len() % 2, 0);
    digits
        .chunks_exact(2)
        .map(|pair| (hex_nibble(pair[0]) << 4) | hex_nibble(pair[1]))
        .collect()
}

pub fn hex_array<const N: usize>(s: &str) -> [u8; N] {
    let bytes = hex_vec(s);
    assert_eq!(bytes.len(), N);
    let mut out = [0u8; N];
    out.copy_from_slice(&bytes);
    out
}

fn hex_nibble(b: u8) -> u8 {
    match b {
        b'0'..=b'9' => b - b'0',
        b'a'..=b'f' => b - b'a' + 10,
        b'A'..=b'F' => b - b'A' + 10,
        _ => panic!("bad hex byte"),
    }
}

pub fn verify(policy: VerifyPolicy, input: VerifyInput<'_>) -> bool {
    let mut verifier = Verifier::with_cache(policy, NullKeyCache::new());
    let mut out = [false];
    verifier.verify_batch(&[input], &mut out);
    out[0]
}

pub fn verify_batch(policy: VerifyPolicy, inputs: &[VerifyInput<'_>]) -> Vec<bool> {
    let mut verifier = Verifier::with_cache(policy, NullKeyCache::new());
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
