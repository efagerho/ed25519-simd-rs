use ed25519_simd::Zip215Policy;

pub mod support;

support::benchmark_main!(hot, Zip215Policy);
