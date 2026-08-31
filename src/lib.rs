#![doc = include_str!("../README.md")]
#[cfg(all(
    not(doc),
    not(all(
        target_arch = "x86_64",
        target_feature = "avx512f",
        target_feature = "avx512bw",
        target_feature = "avx512dq",
        target_feature = "avx512ifma",
    )),
))]
compile_error!(
    "ed25519-simd requires x86_64 with AVX-512F, AVX-512BW, AVX-512DQ, and AVX-512IFMA enabled"
);

mod batch;
mod cache;
mod edwards;
mod field;
mod hot_key_cache;
mod input;
mod scalar;
mod sha512;
mod verifier;
mod wide;

pub use cache::{CachedPublicKey, KeyCache, NullKeyCache};
pub use hot_key_cache::HotKeyCache;
pub use input::{PUBLIC_KEY_LEN, SIGNATURE_LEN, VerifyInput};
pub use verifier::{
    DalekPolicy, DalekVerifier, RuntimeVerifier, VerificationPolicy, Verifier, VerifyPolicy,
    Zip215Policy, Zip215Verifier,
};
