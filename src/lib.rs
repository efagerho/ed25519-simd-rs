#![doc = include_str!("../README.md")]
#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512dq",
    target_feature = "avx512ifma",
)))]
compile_error!("ed25519-simd requires x86_64 with AVX-512F, AVX-512DQ, and AVX-512IFMA enabled");

mod batch;
mod cache;
mod cpuid;
mod edwards;
mod field;
mod hot_key_cache;
mod policy;
mod scalar;
mod sha512;
mod verifier;
mod wide;

pub use batch::{PUBLIC_KEY_LEN, SIGNATURE_LEN};
pub use cache::{CachedPublicKey, KeyCache, NullKeyCache};
pub use hot_key_cache::{CacheStats, HotKeyCache};
pub use policy::VerifyPolicy;
pub use verifier::{Verifier, VerifyInput};
