use ed25519_simd::DalekPolicy;

pub mod support;

support::benchmark_main!(DalekPolicy, true);
