use core::convert::TryFrom;
use std::sync::Once;

use curve25519::ed_sigs::{Signature, VerificationKey, VerificationKeyBytes, batch};
use ed25519_dalek::{
    Signature as DalekSignature, Verifier as DalekVerifier, VerifyingKey as DalekVerifyingKey,
    verify_batch as dalek_verify_batch,
};
use ed25519_simd::VerifyInput;
use openssl::{
    pkey::{Id as OpenSslId, PKey},
    sign::Verifier as OpenSslVerifier,
};
use sodiumoxide::crypto::sign::ed25519::{
    PublicKey as SodiumPublicKey, Signature as SodiumSignature, verify_detached as sodium_verify,
};

/// One-time libsodium initialization, kept outside timed loops.
pub(super) fn init_sodiumoxide() {
    static INIT: Once = Once::new();
    INIT.call_once(|| sodiumoxide::init().expect("failed to initialize libsodium"));
}
pub(super) fn solana_ed25519_batch_zip215(inputs: &[VerifyInput<'_>]) -> bool {
    let mut batch = batch::Verifier::new();
    for input in inputs {
        let vk_bytes = VerificationKeyBytes::from(input.public_key);
        let sig = Signature::from(input.signature);
        batch.queue((vk_bytes, sig, input.message));
    }
    batch.verify(rand::thread_rng()).is_ok()
}

// Verify every element without short-circuiting; parse inside the timed loop.
pub(super) fn solana_ed25519_dalek_loop(inputs: &[VerifyInput<'_>]) -> bool {
    inputs.iter().fold(true, |acc, input| {
        let vk_bytes = VerificationKeyBytes::from(input.public_key);
        let sig = Signature::from(input.signature);
        let ok = VerificationKey::try_from(vk_bytes)
            .and_then(|vk| vk.verify_dalek(&sig, input.message))
            .is_ok();
        acc & ok
    })
}

pub(super) fn dalek_batch(inputs: &[VerifyInput<'_>]) -> bool {
    let messages: Vec<&[u8]> = inputs.iter().map(|input| input.message).collect();
    let signatures: Vec<DalekSignature> = inputs
        .iter()
        .map(|input| DalekSignature::from_bytes(&input.signature))
        .collect();
    let verifying_keys: Vec<DalekVerifyingKey> = inputs
        .iter()
        .map(|input| DalekVerifyingKey::from_bytes(&input.public_key).unwrap())
        .collect();
    dalek_verify_batch(&messages, &signatures, &verifying_keys).is_ok()
}

pub(super) fn dalek_loop(inputs: &[VerifyInput<'_>]) -> bool {
    inputs.iter().fold(true, |acc, input| {
        let signature = DalekSignature::from_bytes(&input.signature);
        let ok = DalekVerifyingKey::from_bytes(&input.public_key)
            .map(|vk| DalekVerifier::verify(&vk, input.message, &signature).is_ok())
            .unwrap_or(false);
        acc & ok
    })
}

pub(super) fn aws_lc_loop(inputs: &[VerifyInput<'_>]) -> bool {
    inputs.iter().fold(true, |acc, input| {
        let ok = aws_lc_rs::signature::ParsedPublicKey::new(
            &aws_lc_rs::signature::ED25519,
            input.public_key,
        )
        .map(|key| key.verify_sig(input.message, &input.signature).is_ok())
        .unwrap_or(false);
        acc & ok
    })
}

pub(super) fn ring_loop(inputs: &[VerifyInput<'_>]) -> bool {
    inputs.iter().fold(true, |acc, input| {
        let key =
            ring::signature::UnparsedPublicKey::new(&ring::signature::ED25519, input.public_key);
        acc & key.verify(input.message, &input.signature).is_ok()
    })
}

pub(super) fn sodium_loop(inputs: &[VerifyInput<'_>]) -> bool {
    inputs.iter().fold(true, |acc, input| {
        let key = SodiumPublicKey::from_slice(&input.public_key).unwrap();
        let signature = SodiumSignature::from_bytes(&input.signature).unwrap();
        acc & sodium_verify(&signature, input.message, &key)
    })
}

pub(super) fn openssl_loop(inputs: &[VerifyInput<'_>]) -> bool {
    inputs.iter().fold(true, |acc, input| {
        let ok = (|| {
            let key = PKey::public_key_from_raw_bytes(&input.public_key, OpenSslId::ED25519)?;
            let mut verifier = OpenSslVerifier::new_without_digest(&key)?;
            verifier.verify_oneshot(&input.signature, input.message)
        })()
        .unwrap_or(false);
        acc & ok
    })
}
