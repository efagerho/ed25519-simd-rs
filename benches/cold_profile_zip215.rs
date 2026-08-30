//! Plain profiling harness for the ZIP-215 `NullKeyCache` path.
//! Build: `cargo bench --bench cold_profile_zip215 --no-run`

#[path = "support/profile.rs"]
pub mod profile;

use ed25519_simd::Zip215Policy;

fn main() {
    profile::run_cold::<Zip215Policy>();
}
