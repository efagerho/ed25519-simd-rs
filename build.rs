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
        if routine == "pow2" {
            println!("cargo:rerun-if-changed=src/wide/avx512ifma/pow22523.inc");
        }
        if matches!(routine, "double4" | "cached-add") {
            println!("cargo:rerun-if-changed=src/wide/avx512ifma/fe51_product.inc");
        }
        for path in [
            source.into(),
            format!("verification/crate/{proof}"),
            "verification/machine".into(),
            "verification/arithmetic".into(),
            "verification/curve25519".into(),
            "verification/crate/Wide51.v".into(),
            "verification/crate/FieldSymbolic.v".into(),
            "verification/crate/FieldKernel.v".into(),
            "verification/crate/PointFrame.v".into(),
            "verification/crate/_CoqProject".into(),
            "verification/proof_build.py".into(),
            "verification/elf.py".into(),
            // The component drivers share the listing tools in pow2.
            "verification/crate/pow2".into(),
        ] {
            println!("cargo:rerun-if-changed={path}");
        }
        println!("cargo:rerun-if-env-changed=LLVM_MC");
        println!("cargo:rerun-if-env-changed=ED25519_SIMD_COQ_LIBRARIES");
        let status = Command::new("python3")
            .arg("-B")
            .arg(format!("verification/crate/{proof}/review.py"))
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
