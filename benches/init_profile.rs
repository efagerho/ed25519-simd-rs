//! Plain harness for measuring one-process [`Verifier`] initialization.
//! Build: `cargo bench --bench init_profile --no-run`
//! Run: `init_profile measure`

use std::hint::black_box;
use std::time::Instant;

use ed25519_simd::Zip215Verifier;

fn main() {
    if std::env::args().nth(1).as_deref() != Some("measure") {
        eprintln!("usage: init_profile measure");
        return;
    }

    let start = Instant::now();
    let verifier = black_box(Zip215Verifier::new());
    let elapsed = start.elapsed();
    black_box(verifier);

    eprintln!("{:.3} ms", elapsed.as_secs_f64() * 1_000.0);
}
