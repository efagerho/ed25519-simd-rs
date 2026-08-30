//! Plain profiling harness for steady-state Dalek `HotKeyCache` hits.
//! Build: `cargo bench --bench hot_profile_dalek --no-run`

#[path = "support/profile.rs"]
pub mod profile;

use ed25519_simd::DalekPolicy;

fn main() {
    profile::run_hot::<DalekPolicy>();
}
