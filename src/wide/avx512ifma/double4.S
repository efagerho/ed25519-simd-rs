// Four doublings, independently in each of eight lanes, modulo p = 2^255-19.
// Experimental: this assembly is not yet formally verified.
// The pow2 Coq theorem does not cover this symbol.
//
// SysV AMD64: RDI points to an exclusive 1280-byte WidePoint. Fields X/Y/Z/T
// start at 0/320/640/960, with five little-endian u64x8 limb vectors each.
// For X/Y/Z: limb0 < 2^60, limb1 + (limb0 >> 51) < 2^52, limbs2..4 < 2^52.
// No curve-membership assumption. Incoming T is never read. Every output
// limb0,2,3,4 < 2^51, limb1 < 2^52; all 1280 output bytes are written.
//
// Each round computes A=X^2, B=Y^2, C=Z^2, D=(X+Y)^2, then
// E=D-A-B, G=B-A, F=G-2*C, H=-A-B; X'=E*F, Y'=G*H, Z'=F*G.
// Only the fourth round computes T'=E*H. Arithmetic uses radix 2^51.
//
// Clobbers RAX, RCX, RSI, R8, arithmetic flags and ZMM0..31. Preserves all
// SysV callee-saved registers and restores RSP. Scratch is 1280 bytes aligned
// to 64 bytes. Saving RBP, alignment padding (at most 48 bytes with a SysV
// caller) and two nested return addresses use at most 1352 bytes below entry
// RSP. The point region must be disjoint from this routine's scratch and
// return-address slots.
// Internal labels use a private convention: RSI always points to scratch,
// RDI/RSI/RCX survive kernels, and every vector memory access is unaligned.
// Branches and memory addresses depend only on the fixed schedule/pointers.
.text
.p2align 4
.globl ed25519_simd_double4_ifma
.hidden ed25519_simd_double4_ifma
.type ed25519_simd_double4_ifma,@function

// Numeric macro arguments keep register allocation visible in the source.
.macro d4_rrr op, dst, a, b
    \op zmm\dst, zmm\a, zmm\b
.endm
.macro d4_rri op, dst, a, n
    \op zmm\dst, zmm\a, \n
.endm
.macro d4_rr op, dst, a
    \op zmm\dst, zmm\a
.endm
.macro d4_read dst, base, offset
    vmovdqu64 zmm\dst, [\base + \offset]
.endm
.macro d4_write base, offset, src
    vmovdqu64 [\base + \offset], zmm\src
.endm

.macro d4_load base, offset, first
.irp i,0,1,2,3,4
    d4_read %(\first+\i), \base, %(\offset+64*\i)
.endr
.endm
.macro d4_store base, offset, first
.irp i,0,1,2,3,4
    d4_write \base, %(\offset+64*\i), %(\first+\i)
.endr
.endm

// Carry all five limbs independently. Input limbs < 2^63; output limbs1..4
// are < 2^51 + 4096, and limb0 < 2^51 + 19*4096. These bounds suffice for
// IFMA52 (and for square's limb0 carry); a serial carry chain is unnecessary.
// ZMM20..24 are scratch; 28=19, 29=2^51-1.
.macro d4_reduce first
.irp i,0,1,2,3,4
    d4_rri vpsrlq, %(20+\i), %(\first+\i), 51
    d4_rrr vpandq, %(\first+\i), %(\first+\i), 29
.endr
.irp i,0,1,2,3
    d4_rrr vpaddq, %(\first+\i+1), %(\first+\i+1), %(20+\i)
.endr
    vpmullq zmm24, zmm24, zmm28
    vpaddq zmm\first, zmm\first, zmm24
.endm

.altmacro
ed25519_simd_double4_ifma:
    push rbp
    mov rbp, rsp
    and rsp, -64
    sub rsp, 1280
    mov rsi, rsp
    mov eax, 19
    vpbroadcastq zmm28, rax
    mov rax, 0x7ffffffffffff
    vpbroadcastq zmm29, rax
    mov ecx, 3
.Ld4_repeat:
    call .Ld4_prepare
    call .Ld4_multiply_single
    d4_store rdi, 320, 0
    dec ecx
    jne .Ld4_repeat
    call .Ld4_prepare
    d4_load rsi, 0, 5
    call .Ld4_multiply_pair
    d4_store rdi, 320, 0
    d4_store rdi, 960, 5
    mov rsp, rbp
    pop rbp
    vzeroupper
    ret

// Read X/Y/Z before the first point store. Scratch initially holds A/B and
// X+Y, then E/G/F/H at 0/320/640/960. Return with X' and Z' already stored,
// G in ZMM0..4 and R8 pointing to H, ready for Y'. The last round also
// reloads E into ZMM5..9 to compute T'; earlier rounds never need that load.
.Ld4_prepare:
    d4_load rdi, 0, 0
    d4_load rdi, 320, 5
.irp i,0,1,2,3,4
    d4_rrr vpaddq, %(10+\i), \i, %(5+\i)
.endr
    d4_reduce 10
    d4_store rsi, 960, 10
    call .Ld4_square_pair
    d4_store rsi, 0, 0
    d4_store rsi, 320, 5
    d4_load rdi, 640, 0
    d4_load rsi, 960, 5
    call .Ld4_square_pair

    // Bias limbs represent 2048*p. Kernels return limbs < 2^52, so even
    // A+2*C < 3*2^52 is below either bias;
    // bias + D/B < 2^63. No intermediate add, shift or subtract wraps.
    mov rax, 0x3fffffffffff6800
    vpbroadcastq zmm30, rax
    mov rax, 0x3ffffffffffff800
    vpbroadcastq zmm31, rax
.irp i,0,1,2,3,4
    vmovdqu64 zmm20, [rsi + 64*\i]
    vmovdqu64 zmm21, [rsi + 320 + 64*\i]
.if \i == 0
    vpsubq zmm22, zmm30, zmm20
.else
    vpsubq zmm22, zmm31, zmm20
.endif
    // Share bias-A between G=B+(bias-A) and H=(bias-A)-B.
    // E=D+H; F uses G before its carry pass, with the same bias.
    d4_rrr vpaddq, %(10+\i), 21, 22
    vpsllq zmm23, zmm\i, 1
    d4_rrr vpsubq, %(15+\i), %(10+\i), 23
    vpsubq zmm22, zmm22, zmm21
    d4_rrr vpaddq, \i, %(5+\i), 22
    d4_rr vmovdqa64, %(5+\i), 22
.endr
    d4_reduce 0
    d4_reduce 5
    d4_reduce 10
    d4_reduce 15
    d4_store rsi, 0, 0
    d4_store rsi, 320, 10
    d4_store rsi, 640, 15
    d4_store rsi, 960, 5
.irp i,0,1,2,3,4
    d4_rr vmovdqa64, %(5+\i), %(10+\i)
.endr
    lea r8, [rsi + 640]
    call .Ld4_multiply_pair
    d4_store rdi, 0, 0
    d4_store rdi, 640, 5
    d4_load rsi, 320, 0
    lea r8, [rsi + 960]
    ret

// ZMM0..4 and (for a pair) 5..9 are inputs/outputs. Multiplication uses
// one shared right operand at R8. Accumulate exact columns as lo+2^52*hi,
// folding degree >=5 by 19. ZMM10..19 hold output limbs until all source
// limbs have been consumed. Interleave both products' low/high accumulators
// in ZMM20/21 and ZMM22/23 to expose four independent IFMA chains.
//
// Single: cache the right operand in unused ZMM5..9; carry in ZMM24.
// Pair: cache right limbs0..4 in ZMM24/26/27/30/31. The second product's
// carry stays in ZMM25. The first product's carry after columns0..3 uses
// ZMM16..19: each is a future second-product output, read before that output
// is written. Column4 puts the final carry in ZMM24, after right limb0's
// last use. Thus each right limb needs only one load per kernel call.
.macro d4_term i, streams, right
.irp high,0,1
.irp s,0,1
.if \s < \streams
.if \high
    d4_rrr vpmadd52huq, %(21+2*\s), %(5*\s+\i), \right
.else
    d4_rrr vpmadd52luq, %(20+2*\s), %(5*\s+\i), \right
.endif
.endif
.endr
.endr
.endm

.macro d4_column k, streams
.irp s,0,1
.if \s < \streams
    d4_rrr vpxorq, %(20+2*\s), %(20+2*\s), %(20+2*\s)
    d4_rrr vpxorq, %(21+2*\s), %(21+2*\s), %(21+2*\s)
.endif
.endr
.irp wrapped,1,0
.irp i,0,1,2,3,4
.irp j,0,1,2,3,4
.if \i+\j == \k+5*\wrapped
.if \streams == 1
    d4_term \i, 1, %(5+\j)
.elseif \j == 0
    d4_term \i, \streams, 24
.elseif \j < 3
    d4_term \i, \streams, %(25+\j)
.else
    d4_term \i, \streams, %(27+\j)
.endif
.endif
.endr
.endr
.if \wrapped && (\k < 4)
.irp s,0,1
.if \s < \streams
    d4_rrr vpmullq, %(20+2*\s), %(20+2*\s), 28
    d4_rrr vpmullq, %(21+2*\s), %(21+2*\s), 28
.endif
.endr
.endif
.endr
.irp s,0,1
.if \s < \streams
.if \k
.if (\streams == 2) && (\s == 0)
    // Consume the first product's carry before the second writes this slot.
    d4_rrr vpaddq, 20, 20, %(15+\k)
.else
    d4_rrr vpaddq, %(20+2*\s), %(20+2*\s), %(24+\s)
.endif
.endif
    d4_rrr vpandq, %(10+5*\s+\k), %(20+2*\s), 29
.if (\streams == 2) && (\s == 0) && (\k < 4)
    // Borrow the second product's next output slot; keep right limb0 live.
    d4_rri vpsrlq, %(16+\k), 20, 51
    d4_rri vpsllq, 21, 21, 1
    d4_rrr vpaddq, %(16+\k), %(16+\k), 21
.else
    d4_rri vpsrlq, %(24+\s), %(20+2*\s), 51
    d4_rri vpsllq, %(21+2*\s), %(21+2*\s), 1
    d4_rrr vpaddq, %(24+\s), %(24+\s), %(21+2*\s)
.endif
.endif
.endr
.endm

.macro d4_multiply_kernel streams
.if \streams == 1
    d4_load r8, 0, 5
.else
    vmovdqu64 zmm24, [r8]
    vmovdqu64 zmm26, [r8 + 64]
    vmovdqu64 zmm27, [r8 + 128]
    vmovdqu64 zmm30, [r8 + 192]
    vmovdqu64 zmm31, [r8 + 256]
.endif
.irp k,0,1,2,3,4
    d4_column \k, \streams
.endr
.irp s,0,1
.if \s < \streams
    d4_rrr vpmullq, %(24+\s), %(24+\s), 28
    d4_rrr vpaddq, %(10+5*\s), %(10+5*\s), %(24+\s)
    d4_rri vpsrlq, %(24+\s), %(10+5*\s), 51
    d4_rrr vpandq, %(5*\s), %(10+5*\s), 29
    d4_rrr vpaddq, %(5*\s+1), %(10+5*\s+1), %(24+\s)
.irp i,2,3,4
    d4_rr vmovdqa64, %(5*\s+\i), %(10+5*\s+\i)
.endr
.endif
.endr
    ret
.endm

// A loose-input square. Carry limb0 first; every IFMA source then fits in
// 52 bits. Only limb0 can be doubled as a source. All other cross-products
// are doubled in their accumulators, including those involving limbs2/4.
// For polynomial degrees k, H[k] is the high 52-bit product sum. Assemble
// radix-2^51 columns as L[k] + 2*H[k-1], then fold degrees >=5 by 19.
.macro d4_square_field x0, x1, x2, x3, x4
    vpsrlq zmm10, \x0, 51
    vpandq \x0, \x0, zmm29
    vpaddq \x1, \x1, zmm10
    vpsllq zmm10, \x0, 1

    // H[0..8] in ZMM13..21.
    vpxorq zmm13, zmm13, zmm13
    vpmadd52huq zmm13, \x0, \x0
    vpxorq zmm14, zmm14, zmm14
    vpmadd52huq zmm14, zmm10, \x1
    vpxorq zmm15, zmm15, zmm15
    vpmadd52huq zmm15, zmm10, \x2
    vpmadd52huq zmm15, \x1, \x1
    vpxorq zmm16, zmm16, zmm16
    vpmadd52huq zmm16, \x1, \x2
    vpsllq zmm16, zmm16, 1
    vpmadd52huq zmm16, zmm10, \x3
    vpxorq zmm17, zmm17, zmm17
    vpmadd52huq zmm17, \x1, \x3
    vpsllq zmm17, zmm17, 1
    vpmadd52huq zmm17, zmm10, \x4
    vpmadd52huq zmm17, \x2, \x2
    vpxorq zmm18, zmm18, zmm18
    vpmadd52huq zmm18, \x1, \x4
    vpmadd52huq zmm18, \x2, \x3
    vpsllq zmm18, zmm18, 1
    vpxorq zmm19, zmm19, zmm19
    vpmadd52huq zmm19, \x2, \x4
    vpsllq zmm19, zmm19, 1
    vpmadd52huq zmm19, \x3, \x3
    vpxorq zmm20, zmm20, zmm20
    vpmadd52huq zmm20, \x3, \x4
    vpsllq zmm20, zmm20, 1
    vpxorq zmm21, zmm21, zmm21
    vpmadd52huq zmm21, \x4, \x4

    // Reduced columns4..0 in ZMM26..22. Add cross-product low halves to
    // H before doubling where both terms need the same factor of two.
    vmovdqa64 zmm26, zmm16
    vpmadd52luq zmm26, \x1, \x3
    vpsllq zmm26, zmm26, 1
    vpmadd52luq zmm26, zmm10, \x4
    vpmadd52luq zmm26, \x2, \x2
    vpsllq zmm27, zmm21, 1
    vpmullq zmm27, zmm27, zmm28
    vpaddq zmm26, zmm26, zmm27
    vmovdqa64 zmm25, zmm15
    vpmadd52luq zmm25, \x1, \x2
    vpsllq zmm25, zmm25, 1
    vpmadd52luq zmm25, zmm10, \x3
    vpsllq zmm27, zmm20, 1
    vpmadd52luq zmm27, \x4, \x4
    vpmullq zmm27, zmm27, zmm28
    vpaddq zmm25, zmm25, zmm27
    vpsllq zmm24, zmm14, 1
    vpmadd52luq zmm24, zmm10, \x2
    vpmadd52luq zmm24, \x1, \x1
    vmovdqa64 zmm27, zmm19
    vpmadd52luq zmm27, \x3, \x4
    vpsllq zmm27, zmm27, 1
    vpmullq zmm27, zmm27, zmm28
    vpaddq zmm24, zmm24, zmm27
    vpsllq zmm23, zmm13, 1
    vpmadd52luq zmm23, zmm10, \x1
    vmovdqa64 zmm27, zmm18
    vpmadd52luq zmm27, \x2, \x4
    vpsllq zmm27, zmm27, 1
    vpmadd52luq zmm27, \x3, \x3
    vpmullq zmm27, zmm27, zmm28
    vpaddq zmm23, zmm23, zmm27
    vpxorq zmm22, zmm22, zmm22
    vpmadd52luq zmm22, \x0, \x0
    vmovdqa64 zmm27, zmm17
    vpmadd52luq zmm27, \x1, \x4
    vpmadd52luq zmm27, \x2, \x3
    vpsllq zmm27, zmm27, 1
    vpmullq zmm27, zmm27, zmm28
    vpaddq zmm22, zmm22, zmm27

    // Each L[k], H[k] < 5*2^52, so folded columns < 300*2^52 < 2^61.
    // Carry additions stay < 2^62 and 19*carry4 < 2^16: the IFMA fold
    // below is exact. Independent carries 1->2 and 3->4->0 finish the square.
    // These internal square outputs
    // may leave limbs1/3 slightly above 2^51, but every limb stays <2^52.
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

.p2align 4, 0x90
.Ld4_square_pair:
    d4_square_field zmm0, zmm1, zmm2, zmm3, zmm4
    d4_square_field zmm5, zmm6, zmm7, zmm8, zmm9
    ret
.Ld4_multiply_pair:
    d4_multiply_kernel 2
.Ld4_multiply_single:
    d4_multiply_kernel 1
.noaltmacro
.size ed25519_simd_double4_ifma, .-ed25519_simd_double4_ifma
.purgem d4_load
.purgem d4_store
.purgem d4_reduce
.purgem d4_term
.purgem d4_column
.purgem d4_multiply_kernel
.purgem d4_square_field
.purgem d4_rrr
.purgem d4_rri
.purgem d4_rr
.purgem d4_read
.purgem d4_write
