// SysV AMD64. rdi = output pair, rsi, rdx = input fields.
// A field has five consecutive 64-byte limb vectors. zmm0..9 hold the
// current pair across every internal call. Three earlier pairs live on stack.
.text
.p2align 4
.globl ed25519_simd_pow2_ifma
.hidden ed25519_simd_pow2_ifma
.type ed25519_simd_pow2_ifma,@function

.macro pair_save base, offset
.irp i,0,1,2,3,4,5,6,7,8,9
    vmovdqu64 [\base + \offset + 64*\i], zmm\i
.endr
.endm

.macro squares n
    mov ecx, \n
.Lrepeat\@:
    call .Lsquare
    dec ecx
    jne .Lrepeat\@
.endm
.macro multiply_slot n
    lea r8, [rsp + 640*\n]
    call .Lmultiply
.endm

ed25519_simd_pow2_ifma:
    sub rsp, 1928
    mov eax, 19
    vpbroadcastq zmm28, rax
    mov rax, 0x7ffffffffffff
    vpbroadcastq zmm29, rax
.irp i,0,1,2,3,4
    vmovdqu64 zmm\i, [rsi + 64*\i]
.endr
.irp i,5,6,7,8,9
    vmovdqu64 zmm\i, [rdx + 64*(\i-5)]
.endr
    pair_save rsp, 0
    // Raw input may use all 52 bits in every limb. The general product
    // establishes the tighter bounds needed for doubled square operands.
    multiply_slot 0
    pair_save rsp, 640
    squares 2
    multiply_slot 0
    pair_save rsp, 1280
    multiply_slot 1
    squares 1
    multiply_slot 2
    // Current exponent is 31. Build exponents 2^k - 1.
    pair_save rsp, 640
    squares 5
    multiply_slot 1
    pair_save rsp, 640
    squares 10
    multiply_slot 1
    pair_save rsp, 1280
    squares 20
    multiply_slot 2
    squares 10
    multiply_slot 1
    pair_save rsp, 640
    squares 50
    multiply_slot 1
    pair_save rsp, 1280
    squares 100
    multiply_slot 2
    squares 50
    multiply_slot 1
    squares 2
    multiply_slot 0
    pair_save rdi, 0
    add rsp, 1928
    vzeroupper
    ret

// Columns fold terms of degree >= 5 using (2^51)^5 = 19 mod p.
// For each stream, low + 2^52 * high is the exact column sum.
// Headroom for every accumulation and carry is checked by the proof.
.macro term ai, aj, bi, bj
    vmovdqu64 zmm30, [r8 + 64*\aj]
    vmovdqu64 zmm31, [r8 + 64*\bj]
    vpmadd52luq zmm20, zmm\ai, zmm30
    vpmadd52luq zmm22, zmm\bi, zmm31
    vpmadd52huq zmm21, zmm\ai, zmm30
    vpmadd52huq zmm23, zmm\bi, zmm31
.endm

.macro column k, outa, outb
.irp r,20,21,22,23
    vpxorq zmm\r, zmm\r, zmm\r
.endr
.irp wrapped,1,0
.irp i,0,1,2,3,4
.irp j,0,1,2,3,4
.if (\i+\j) == (\k+5*\wrapped)
    term \i, \j, %(\i+5), %(\j+5)
.endif
.endr
.endr
.if (\wrapped) * (\k < 4)
.irp r,20,21,22,23
    vpmullq zmm\r, zmm\r, zmm28
.endr
.endif
.endr
.if \k
    vpaddq zmm20, zmm20, zmm24
    vpaddq zmm22, zmm22, zmm25
.endif
    vpandq zmm\outa, zmm20, zmm29
    vpandq zmm\outb, zmm22, zmm29
    vpsrlq zmm24, zmm20, 51
    vpsrlq zmm25, zmm22, 51
    vpsllq zmm21, zmm21, 1
    vpsllq zmm23, zmm23, 1
    vpaddq zmm24, zmm24, zmm21
    vpaddq zmm25, zmm25, zmm23
.endm

.macro multiply_pair
.irp k,0,1,2,3,4
    column \k, %(10+\k), %(15+\k)
.endr
    vpmullq zmm24, zmm24, zmm28
    vpmullq zmm25, zmm25, zmm28
    vpaddq zmm10, zmm10, zmm24
    vpaddq zmm15, zmm15, zmm25
    vpsrlq zmm24, zmm10, 51
    vpsrlq zmm25, zmm15, 51
    vpandq zmm0, zmm10, zmm29
    vpandq zmm5, zmm15, zmm29
    vpaddq zmm1, zmm11, zmm24
    vpaddq zmm6, zmm16, zmm25
.irp i,2,3,4,7,8,9
    copy_limb \i, %(10+\i)
.endr
    ret
.endm
.macro copy_limb dst, src
    vmovdqa64 zmm\dst, zmm\src
.endm

// Square one eight-lane field. Limbs 0, 2 and 4 fit in 51 bits and
// can be doubled before IFMA. The carry chains restore these bounds.
.macro square_field x0, x1, x2, x3, x4
    vpsllq zmm10, \x0, 1
    vpsllq zmm11, \x2, 1
    vpsllq zmm12, \x4, 1

    // High 52-bit halves by polynomial degree, H[0..8] in zmm13..21.
    vpxorq zmm13, zmm13, zmm13
    vpmadd52huq zmm13, \x0, \x0
    vpxorq zmm14, zmm14, zmm14
    vpmadd52huq zmm14, zmm10, \x1
    vpxorq zmm15, zmm15, zmm15
    vpmadd52huq zmm15, zmm10, \x2
    vpmadd52huq zmm15, \x1, \x1
    vpxorq zmm16, zmm16, zmm16
    vpmadd52huq zmm16, zmm10, \x3
    vpmadd52huq zmm16, \x1, zmm11
    // Both x1 and x3 may use 52 bits. Double their product halves
    // after IFMA so neither source overflows.
    vpxorq zmm17, zmm17, zmm17
    vpmadd52huq zmm17, \x1, \x3
    vpsllq zmm17, zmm17, 1
    vpmadd52huq zmm17, zmm10, \x4
    vpmadd52huq zmm17, \x2, \x2
    vpxorq zmm18, zmm18, zmm18
    vpmadd52huq zmm18, \x1, zmm12
    vpmadd52huq zmm18, zmm11, \x3
    vpxorq zmm19, zmm19, zmm19
    vpmadd52huq zmm19, zmm11, \x4
    vpmadd52huq zmm19, \x3, \x3
    vpxorq zmm20, zmm20, zmm20
    vpmadd52huq zmm20, \x3, zmm12
    vpxorq zmm21, zmm21, zmm21
    vpmadd52huq zmm21, \x4, \x4

    // For radix B = 2^51, C[k] = L[k] + 2*H[k-1]. Form the five
    // limbs C[k] + 19*C[k+5] in descending order (zmm26..22).
    // Degree four doubles the x1*x3 low half together with H[3].
    vmovdqa64 zmm26, zmm16
    vpmadd52luq zmm26, \x1, \x3
    vpsllq zmm26, zmm26, 1
    vpmadd52luq zmm26, zmm10, \x4
    vpmadd52luq zmm26, \x2, \x2
    vpsllq zmm27, zmm21, 1
    vpmullq zmm27, zmm27, zmm28
    vpaddq zmm26, zmm26, zmm27
    vpsllq zmm25, zmm15, 1
    vpmadd52luq zmm25, zmm10, \x3
    vpmadd52luq zmm25, \x1, zmm11
    vpsllq zmm27, zmm20, 1
    vpmadd52luq zmm27, \x4, \x4
    vpmullq zmm27, zmm27, zmm28
    vpaddq zmm25, zmm25, zmm27
    vpsllq zmm24, zmm14, 1
    vpmadd52luq zmm24, zmm10, \x2
    vpmadd52luq zmm24, \x1, \x1
    vpsllq zmm27, zmm19, 1
    vpmadd52luq zmm27, \x3, zmm12
    vpmullq zmm27, zmm27, zmm28
    vpaddq zmm24, zmm24, zmm27
    vpsllq zmm23, zmm13, 1
    vpmadd52luq zmm23, zmm10, \x1
    vpsllq zmm27, zmm18, 1
    vpmadd52luq zmm27, zmm11, \x4
    vpmadd52luq zmm27, \x3, \x3
    vpmullq zmm27, zmm27, zmm28
    vpaddq zmm23, zmm23, zmm27
    vpxorq zmm22, zmm22, zmm22
    vpmadd52luq zmm22, \x0, \x0
    vpsllq zmm27, zmm17, 1
    vpmadd52luq zmm27, \x1, zmm12
    vpmadd52luq zmm27, zmm11, \x3
    vpmullq zmm27, zmm27, zmm28
    vpaddq zmm22, zmm22, zmm27

    // Independent carries along 1 -> 2 and 3 -> 4 -> 0. The latter
    // folds 19*carry4 into limb 0; that product fits in 52 bits.
    vpsrlq zmm20, zmm23, 51
    vpandq \x1, zmm23, zmm29
    vpaddq zmm24, zmm24, zmm20
    vpsrlq zmm20, zmm24, 51
    vpandq \x2, zmm24, zmm29
    vpsrlq zmm21, zmm25, 51
    vpandq \x3, zmm25, zmm29
    vpaddq zmm26, zmm26, zmm21
    vpsrlq zmm21, zmm26, 51
    vpandq \x4, zmm26, zmm29
    vpmadd52luq zmm22, zmm21, zmm28
    vpsrlq zmm21, zmm22, 51
    vpandq \x0, zmm22, zmm29
    vpaddq \x1, \x1, zmm21
    vpaddq \x3, \x3, zmm20
.endm

.altmacro
// Use the same padding bytes with rustc's assembler and standalone LLVM MC.
.p2align 4, 0x90
.Lsquare:
    square_field zmm0, zmm1, zmm2, zmm3, zmm4
    square_field zmm5, zmm6, zmm7, zmm8, zmm9
    ret
.Lmultiply:
    multiply_pair
.noaltmacro
.size ed25519_simd_pow2_ifma, .-ed25519_simd_pow2_ifma

.purgem pair_save
.purgem squares
.purgem multiply_slot
.purgem term
.purgem column
.purgem multiply_pair
.purgem square_field
.purgem copy_limb
