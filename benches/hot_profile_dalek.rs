//! Plain profiling harness for steady-state Dalek `HotKeyCache` hits.
//! Build: `cargo bench --bench hot_profile_dalek --no-run`

#[path = "support/profile.rs"]
pub mod profile;

fn main() {
    profile::run_hot::<true>();
}
