use std::{env, process::Command};

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    if env::var("CARGO_CFG_TARGET_OS").as_deref() != Ok("linux")
        || env::var("CARGO_CFG_TARGET_ARCH").as_deref() != Ok("x86_64")
        || env::var("CARGO_CFG_TARGET_POINTER_WIDTH").as_deref() != Ok("64")
    {
        return;
    }
    for (routine, source, proof) in [
        ("pow2", "src/wide/avx512ifma/pow2.S", "pow2"),
        ("double4", "src/wide/avx512ifma/double4.S", "double4"),
        (
            "cached-add",
            "src/wide/avx512ifma/add_cached.S",
            "cached_add",
        ),
        ("scalar", "src/scalar/reduce.S", "scalar"),
    ] {
        let feature = format!(
            "CARGO_FEATURE_VERIFY_ASM_{}",
            routine.replace('-', "_").to_ascii_uppercase()
        );
        if env::var_os(feature).is_none() {
            continue;
        }
        for path in [
            source.into(),
            format!("verification/{proof}"),
            "verification/machine".into(),
            // Arithmetic proofs share the polynomial checker, interval interpreter and ELF helpers.
            "verification/pow2".into(),
            "verification/double4".into(),
        ] {
            println!("cargo:rerun-if-changed={path}");
        }
        println!("cargo:rerun-if-env-changed=LLVM_MC");
        let status = Command::new("python3")
            .arg("-B")
            .arg(format!("verification/{proof}/review.py"))
            .arg(env::var_os("OUT_DIR").unwrap())
            .status()
            .unwrap_or_else(|_| {
                panic!("verify-asm-{routine} requires python3 to run the Coq proof")
            });
        assert!(
            status.success(),
            "verify-asm-{routine} assembly verification failed"
        );
    }
}
