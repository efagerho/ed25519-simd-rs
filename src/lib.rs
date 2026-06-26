#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512dq",
    target_feature = "avx512ifma",
)))]
compile_error!("ed25519-simd requires x86_64 with AVX-512F, AVX-512DQ, and AVX-512IFMA enabled");

mod batch;
mod cache;
mod edwards;
mod field;
mod scalar;
mod sha512;
mod wide;

pub use batch::{PUBLIC_KEY_LEN, SIGNATURE_LEN, VerifyInput, VerifyPolicy};
pub use cache::{CacheStats, CachedPublicKey, KeyCache, LruKeyCache, NullKeyCache, Verifier};
