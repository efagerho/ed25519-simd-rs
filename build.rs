use std::{env, process::Command};

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    if env::var("CARGO_CFG_TARGET_OS").as_deref() != Ok("linux")
        || env::var("CARGO_CFG_TARGET_ARCH").as_deref() != Ok("x86_64")
        || env::var("CARGO_CFG_TARGET_POINTER_WIDTH").as_deref() != Ok("64")
    {
        return;
    }
    for routine in ["pow2", "double4"] {
        let feature = format!("CARGO_FEATURE_VERIFY_ASM_{}", routine.to_ascii_uppercase());
        if env::var_os(feature).is_none() {
            continue;
        }
        for path in [
            format!("src/wide/avx512ifma/{routine}.S"),
            format!("verification/{routine}"),
            "verification/machine".into(),
            // double4 also uses the field polynomial checker and ELF helpers.
            "verification/pow2".into(),
        ] {
            println!("cargo:rerun-if-changed={path}");
        }
        println!("cargo:rerun-if-env-changed=LLVM_MC");
        let status = Command::new("python3")
            .arg("-B")
            .arg(format!("verification/{routine}/review.py"))
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
