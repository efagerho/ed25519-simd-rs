// Assemble with the squaring kernel and addition chain in pow22523.inc.
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

.macro pow2_save slot
    pair_save rsp, (640*\slot)
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
    fe51_pow22523 pow2_save, multiply_slot, squares
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

.altmacro
// Use the same padding bytes with rustc's assembler and standalone LLVM MC.
.p2align 4, 0x90
.Lsquare:
    fe51_square zmm0, zmm1, zmm2, zmm3, zmm4
    fe51_square zmm5, zmm6, zmm7, zmm8, zmm9
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
.purgem pow2_save
.purgem fe51_pow22523
.purgem fe51_square
.purgem copy_limb
