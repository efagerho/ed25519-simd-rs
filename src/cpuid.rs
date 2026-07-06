use std::arch::x86_64::{__cpuid, __cpuid_count, _xgetbv};

/// Panics with a clear message if this host lacks AVX-512 (F, DQ, IFMA) or the
/// required OS state support.
///
/// This reduces, but cannot eliminate, the risk of a raw `SIGILL`: the
/// `-C target-feature`/`-C target-cpu=native` build flags that enable AVX-512
/// apply to the whole binary, not just this crate, so the compiler may legally
/// emit AVX-512 instructions in other code — including the standard library's
/// generic code — that runs before this check, or that never calls into this
/// crate at all. Called once from `Verifier` construction; not a substitute
/// for building on or for the actual deployment CPU.
#[cold]
#[inline(never)]
pub(crate) fn assert_required_avx512_runtime_support() {
    if let Err(reason) = required_avx512_runtime_support() {
        panic!(
            "ed25519-simd was built for AVX-512 (F, DQ, IFMA) but cannot run \
             safely on this host: {reason}; build and run on an AVX-512 IFMA \
             capable CPU with OS AVX-512 state support enabled"
        );
    }
}

#[inline(never)]
fn required_avx512_runtime_support() -> Result<(), &'static str> {
    const CPUID_1_ECX_XSAVE: u32 = 1 << 26;
    const CPUID_1_ECX_OSXSAVE: u32 = 1 << 27;
    const CPUID_1_ECX_AVX: u32 = 1 << 28;
    const CPUID_7_EBX_AVX512F: u32 = 1 << 16;
    const CPUID_7_EBX_AVX512DQ: u32 = 1 << 17;
    const CPUID_7_EBX_AVX512IFMA: u32 = 1 << 21;
    const XCR0_AVX512_STATE: u64 = (1 << 0) | (1 << 1) | (1 << 2) | (1 << 5) | (1 << 6) | (1 << 7);

    unsafe {
        let max_leaf = __cpuid(0).eax;
        if max_leaf < 7 {
            return Err("CPUID leaf 7 is unavailable");
        }

        let leaf1 = __cpuid(1);
        if leaf1.ecx & CPUID_1_ECX_XSAVE == 0 {
            return Err("CPU does not support XSAVE/XGETBV");
        }
        if leaf1.ecx & CPUID_1_ECX_OSXSAVE == 0 {
            return Err("OS has not enabled XSAVE/XGETBV");
        }
        if leaf1.ecx & CPUID_1_ECX_AVX == 0 {
            return Err("CPU does not support AVX");
        }

        let xcr0 = _xgetbv(0);
        if xcr0 & XCR0_AVX512_STATE != XCR0_AVX512_STATE {
            return Err("OS has not enabled AVX-512 register state");
        }

        let leaf7 = __cpuid_count(7, 0);
        if leaf7.ebx & CPUID_7_EBX_AVX512F == 0 {
            return Err("CPU does not support AVX-512F");
        }
        if leaf7.ebx & CPUID_7_EBX_AVX512DQ == 0 {
            return Err("CPU does not support AVX-512DQ");
        }
        if leaf7.ebx & CPUID_7_EBX_AVX512IFMA == 0 {
            return Err("CPU does not support AVX-512IFMA");
        }
    }

    Ok(())
}
