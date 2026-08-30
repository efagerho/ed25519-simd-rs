//! Plain profiling harness for the Dalek `NullKeyCache` path.
//! Build: `cargo bench --bench cold_profile_dalek --no-run`

#[path = "support/profile.rs"]
pub mod profile;

fn main() {
    profile::run_cold::<true>();
}
