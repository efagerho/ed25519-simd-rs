// Eight independent [s]B - [k]A products, from lane-major signed radix-16 digits.
// SysV AMD64. RDI is an exclusive, 64-byte-aligned 1280-byte WidePoint output.
// RSI, RDX, RCX and R8 are the key table pointers, affine base table, s digits
// and k digits with the same layouts as stage_round.S. Cache limbs are < 2^52.
// R9 is 0 (write zero T) or 1 (compute extended T). All digits are public.
// Inputs, output and private stack must be disjoint except for shared inputs.
// The output needs no initialization. Including the staging buffer, saved
// registers, alignment, return slots and callees, at most 5032 bytes below
// entry RSP are used. Each child receives a SysV-aligned stack.
.text
.p2align 4
.globl ed25519_simd_mul_s_base_minus_k_public
.hidden ed25519_simd_mul_s_base_minus_k_public
.type ed25519_simd_mul_s_base_minus_k_public,@function
ed25519_simd_mul_s_base_minus_k_public:
    push rbp
    mov rbp, rsp
    push rbx
    push r12
    push r13
    push r14
    push r15
    push r8                     // [rbp-48] = k digits
    push r9                     // [rbp-56] = final T flag
    and rsp, -64
    sub rsp, 3520               // one staged round, reused across all calls
    mov rbx, rdi                // accumulate directly in the output
    mov r12, rsi
    mov r13, rdx
    mov r14, rcx

    mov rdi, rsp
    mov r9d, 31
    call ed25519_simd_stage_round

    // The selected odd key entry gives (Y-X, Y+X, 2dT, 2Z).
    // Recover (2X, 2Y, 2Z) with 4p added to the subtraction. A radix-51
    // carry pass on each field handles arbitrary 52-bit input limbs.
    mov rax, 4 * ((1 << 51) - 19)
    vpbroadcastq zmm8, rax
    mov rax, 4 * ((1 << 51) - 1)
    vpbroadcastq zmm9, rax
    mov rax, (1 << 51) - 1
    vpbroadcastq zmm10, rax
    vpxorq zmm7, zmm7, zmm7
    // Five fixed rows. ZMM4/5/6 carry X/Y/Z into the next row.
.irp offset,0,64,128,192,256
    vmovdqa64 zmm0, [rsp + \offset]
    vmovdqa64 zmm1, [rsp + 320 + \offset]
    vpaddq zmm2, zmm1, zmm0
.if \offset == 0
    vpaddq zmm1, zmm1, zmm8
    vmovdqa64 zmm3, [rsp + 960]
.else
    vpaddq zmm1, zmm1, zmm9
    vpaddq zmm1, zmm1, zmm4
    vpaddq zmm2, zmm2, zmm5
    vpaddq zmm3, zmm6, [rsp + 960 + \offset]
.endif
    vpsubq zmm1, zmm1, zmm0
    vpsrlq zmm4, zmm1, 51
    vpsrlq zmm5, zmm2, 51
    vpsrlq zmm6, zmm3, 51
    vpandq zmm1, zmm1, zmm10
    vpandq zmm2, zmm2, zmm10
    vpandq zmm3, zmm3, zmm10
    vmovdqa64 [rbx + \offset], zmm1
    vmovdqa64 [rbx + 320 + \offset], zmm2
    vmovdqa64 [rbx + 640 + \offset], zmm3
    vmovdqa64 [rbx + 960 + \offset], zmm7
.endr

    // 2^255 = 19 mod p. Fold the last carries into limb zero. Limbs 1..4
    // are below 2^51, so these loose coordinates satisfy double4's ABI.
    mov eax, 19
    vpbroadcastq zmm0, rax
    vpmullq zmm4, zmm4, zmm0
    vpmullq zmm5, zmm5, zmm0
    vpmullq zmm6, zmm6, zmm0
    vpaddq zmm4, zmm4, [rbx]
    vpaddq zmm5, zmm5, [rbx + 320]
    vpaddq zmm6, zmm6, [rbx + 640]
    vmovdqa64 [rbx], zmm4
    vmovdqa64 [rbx + 320], zmm5
    vmovdqa64 [rbx + 640], zmm6

    // Pair 31 starts at Odd. Form [16]Odd + Base + Even.
    mov rdi, rbx
    call ed25519_simd_double4_ifma
    mov rdi, rbx
    lea rsi, [rsp + 1280]
    mov edx, 1                  // the even addition needs T
    mov ecx, 1                  // affine base
    call ed25519_simd_add_cached_ifma
    mov rdi, rbx
    lea rsi, [rsp + 2240]
    xor edx, edx
    xor ecx, ecx                // projective even key
    call ed25519_simd_add_cached_ifma

    // P <- [256]P + [16]Odd + Base + Even for pairs 30 down to 0.
    mov r15d, 31                // number of remaining pairs
.Lmul_round:
    mov rdi, rsp
    mov rsi, r12
    mov rdx, r13
    mov rcx, r14
    mov r8, [rbp - 48]
    lea r9, [r15 - 1]
    call ed25519_simd_stage_round
    mov rdi, rbx
    mov rsi, rsp
    xor edx, edx
    cmp r15d, 1
    jne .Lmul_step
    mov edx, [rbp - 56]         // pair zero selects the caller's T mode
.Lmul_step:
    call ed25519_simd_ladder_step_ifma
    dec r15d
    jne .Lmul_round

    lea rsp, [rbp - 40]
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    pop rbp
    ret
.size ed25519_simd_mul_s_base_minus_k_public, .-ed25519_simd_mul_s_base_minus_k_public
