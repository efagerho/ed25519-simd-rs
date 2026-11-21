// SysV AMD64: RDI points to n consecutive 64-byte-aligned WidePoints,
// RSI to n unaligned chunks of eight original 32-byte R encodings, RDX=n
// (0..8). Only X,Y,Z are read. The ladder supplies nonzero projective Z
// and radix-51 limbs below 2^52. Bit 8*i+j of RAX is set when candidate
// (i,j) has exactly the supplied encoding and is not small order. Unused
// bits are zero. Both inputs are read-only.
// Exact encoding equality requires y < p, y*Z = Y modulo p, and the
// supplied sign bit equal to the parity of canonical X/Z.
.pushsection .text.ed25519_simd_dalek_recompress,"ax",@progbits
.p2align 4
.globl ed25519_simd_dalek_recompress
.hidden ed25519_simd_dalek_recompress
.type ed25519_simd_dalek_recompress,@function

// Slot zero is the last prefix. The inverse chain overwrites it with z^11
// after its final use of z; the backward pass needs only earlier prefixes.
.macro dc_save slot
.if \slot
    fe51_store rsp, (320*(\slot-1))
.else
    fe51_store r14, 0
.endif
.endm
.macro dc_multiply slot
.if \slot
    lea r8, [rsp + 320*(\slot-1)]
.else
    mov r8, r14
.endif
    call .Lfe51_mul_strict
.endm

ed25519_simd_dalek_recompress:
    xor eax, eax
    test rdx, rdx
    jz .Ldc_empty
    push rbp
    mov rbp, rsp
    push rbx
    push r12
    push r13
    push r14
    push r15
    and rsp, -64
    sub rsp, 3264                   // two work fields, eight prefixes, lane masks
    mov rbx, rdi                    // first candidate
    mov r12, rdi                    // current candidate
    mov r13, rsi                    // current R chunk
    lea r14, [rsp + 640]            // current prefix
    xor r15d, r15d                  // accumulated masks
    fe51_constants
    lea r10, [rsp + 3200]           // two bytes per chunk: Y matches, requested X signs
    xor r9d, r9d                    // any lane with matching canonical Y
.Ldc_forward:
    encoded_point_words r13
    vpmovq2m k1, zmm6
    kmovw eax, k1
    mov [r10 + 1], al
    encoded_y_limbs
    // Canonical y is below p: only the top 19 of the 255-bit encodings fail.
    fe51_high_ones
    vpcmpuq k2{k1}, zmm0, qword ptr [rip + .Lfe51_p0]{1to8}, 5
.irp i,5,6,7,8,9
    vmovdqa64 zmm\i, [r12 + 640 + 64*(\i-5)]
.endr
    // Seed the product with 1024*p - Y. Every limb stays positive for
    // 52-bit Y. The parallel carry leaves a representative in (0,2*p),
    // so encoded_y * Z == Y exactly when its five digits equal p.
    vpsubq zmm10, zmm30, [r12 + 320]
.irp i,11,12,13,14
    vpsubq zmm\i, zmm31, [r12 + 320 + 64*(\i-10)]
.endr
    call .Ltor_seeded_columns
    call .Lfe51_carry
    fe51_high_ones
    vpcmpeqq k1{k1}, zmm0, qword ptr [rip + .Lfe51_p0]{1to8}
    kandnw k1, k2, k1
    kmovw eax, k1
    mov [r10], al
    or r9d, eax

    fe51_load r12, 640
    cmp r12, rbx
    je .Ldc_prefix
    lea r8, [r14 - 320]
    call .Lfe51_mul
.Ldc_prefix:
    dec edx
    jz .Ldc_invert
    fe51_store r14, 0
    add r14, 320
    add r12, 1280
    add r13, 256
    add r10, 2
    jmp .Ldc_forward
.Ldc_invert:
    // A mismatched y rules out the exact encoding for either X sign.
    test r9d, r9d
    jz .Ldc_return
    mov r13, r10                    // walk the saved masks in reverse chunk order
    fe51_pow_chain dc_save, dc_multiply, fe51_squares, 1

    fe51_store rsp, 0
    // The running reciprocal is 1/prefix[i]. Multiplying by prefix[i-1]
    // gives 1/Z[i]; multiplying by Z[i] gives the next reciprocal.
.Ldc_backward:
    mov r8, rsp
    cmp r12, rbx
    je .Ldc_score                   // for i=0 the running reciprocal is 1/Z[0]
    fe51_load r14, -320
    call .Lfe51_mul
    fe51_store rsp, 320
    fe51_load r12, 640
    call .Lfe51_mul                 // both products use the same reciprocal at R8
    fe51_store rsp, 0
    lea r8, [rsp + 320]
.Ldc_score:
    fe51_load r12, 0
    call .Lfe51_mul                 // affine x
    vpcmpuq k1, zmm4, zmm29, 5
    kortestw k1, k1
    jnz .Ldc_reduce_x
.Ldc_x_parity:
    vptestmq k1, zmm0, qword ptr [rip + .Lfe51_one]{1to8}
    kmovw eax, k1
    xor al, [r13 + 1]
    not al
    and al, [r13]
    shl r15, 8
    test al, al
    jz .Ldc_next
    or r15, rax
    mov rdi, r12
    call ed25519_simd_small_order_ifma
    movzx eax, al
    not rax
    and r15, rax
.Ldc_next:
    cmp r12, rbx
    je .Ldc_return
    sub r14, 320
    sub r12, 1280
    sub r13, 2
    fe51_constants                  // SysV permits the callee to clobber ZMM28..31
    jmp .Ldc_backward
.Ldc_return:
    mov rax, r15
    lea rsp, [rbp - 40]
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    pop rbp
    vzeroupper
.Ldc_empty:
    ret
// Lower limbs can carry at most one into the top limb. If every top
// limb is below 2^51-1, each representative is already below p.
.Ldc_reduce_x:
    fe51_modulus_carry
    vpxorq zmm0, zmm0, zmm20
    jmp .Ldc_x_parity
.size ed25519_simd_dalek_recompress, .-ed25519_simd_dalek_recompress
.purgem dc_multiply
.purgem dc_save
.popsection
