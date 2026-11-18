use std::{env, process::Command};

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    if env::var_os("CARGO_FEATURE_VERIFY_ASM_POW2").is_none()
        || env::var("CARGO_CFG_TARGET_OS").as_deref() != Ok("linux")
        || env::var("CARGO_CFG_TARGET_ARCH").as_deref() != Ok("x86_64")
        || env::var("CARGO_CFG_TARGET_POINTER_WIDTH").as_deref() != Ok("64")
    {
        return;
    }
    for path in [
        "src/wide/avx512ifma/pow2.S",
        "verification/pow2/generate_listing.py",
        "verification/pow2/elf.py",
        "verification/machine",
        "verification/pow2/coq",
        "verification/pow2/certify.py",
        "verification/pow2/review.py",
    ] {
        println!("cargo:rerun-if-changed={path}");
    }
    println!("cargo:rerun-if-env-changed=LLVM_MC");
    let status = Command::new("python3")
        .arg("-B")
        .arg("verification/pow2/review.py")
        .arg(env::var_os("OUT_DIR").unwrap())
        .status()
        .expect("verify-asm-pow2 requires python3 to run the Coq proof");
    assert!(
        status.success(),
        "verify-asm-pow2 assembly verification failed"
    );
}
