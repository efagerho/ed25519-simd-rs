//! Plain profiling harness for steady-state ZIP-215 `HotKeyCache` hits.
//! Build: `cargo bench --bench hot_profile_zip215 --no-run`

#[path = "support/profile.rs"]
pub mod profile;

fn main() {
    profile::run_hot::<false>();
}
