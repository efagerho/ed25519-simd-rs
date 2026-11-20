// One radix-256 ladder iteration in eight lanes. Linked proof in verification/crate/ladder_step.
// Calls the separately verified double4 and cached-add implementations.
//
// SysV AMD64 arguments:
//   RDI: exclusive, initialized, 64-byte-aligned 1280-byte WidePoint.
//   RSI: read-only, 64-byte-aligned 3520-byte staged operand buffer:
//          0: odd public-key digit, projective cached (1280 bytes),
//       1280: basepoint digit pair, affine cached (960 bytes),
//       2240: even public-key digit, projective cached (1280 bytes).
//        Each cache is (Y-X), (Y+X), 2*d*T, and projective-only 2*Z,
//        with five 64-byte vectors per field. Every cached limb is < 2^52.
//   RDX: compute_t, exactly 0 or 1, for the final addition.
// The point's X/Y/Z satisfy double4's loose-input bounds: limb0 < 2^60,
// limb1 + (limb0 >> 51) < 2^52, limbs2..4 < 2^52. Incoming T is ignored.
// Point and staged operands must be disjoint from each other and the writable
// stack interval (at most 1384 bytes below entry RSP, including callees).
//
// Schedule: double4; add odd without T; double4; add base with T;
// add even with the requested T mode. For consistent caches of curve points,
// this represents [256]P + [16]Q_odd + Q_base + Q_even. Rust selects the
// negated public-key digits; this wrapper does not negate cached operands.
// All output coordinates have limbs0,2,3,4 < 2^51 and limb1 < 2^52.
// compute_t=0 writes literal zero to T. All output bytes are initialized.
//
// Preserves SysV callee-saved registers and restores RSP. Caller-saved GPRs,
// vector registers and arithmetic flags may be clobbered. The three saved
// GPRs keep every nested call 16-byte aligned, independently of SIMD alignment.
.text
.p2align 4
.globl ed25519_simd_ladder_step_ifma
.hidden ed25519_simd_ladder_step_ifma
.type ed25519_simd_ladder_step_ifma,@function
ed25519_simd_ladder_step_ifma:
    push rbx
    push r12
    push r13
    mov rbx, rdi
    mov r12, rsi
    mov r13, rdx

    call ed25519_simd_double4_ifma

    mov rdi, rbx
    mov rsi, r12
    mov edx, 0
    mov ecx, 0
    call ed25519_simd_add_cached_ifma

    mov rdi, rbx
    call ed25519_simd_double4_ifma

    mov rdi, rbx
    lea rsi, [r12 + 1280]
    mov edx, 1
    mov ecx, 1
    call ed25519_simd_add_cached_ifma

    mov rdi, rbx
    lea rsi, [r12 + 2240]
    mov rdx, r13
    mov ecx, 0
    call ed25519_simd_add_cached_ifma

    pop r13
    pop r12
    pop rbx
    ret
.size ed25519_simd_ladder_step_ifma, .-ed25519_simd_ladder_step_ifma
