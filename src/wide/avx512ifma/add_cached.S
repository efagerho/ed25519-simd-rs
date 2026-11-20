// Cached point addition, independently in eight lanes modulo p = 2^255-19.
// Coq certificate: verification/crate/cached_add, Object.assembled_cached_add_correct.
// The verify-asm-cached-add feature emits only bytes certified by that theorem.
//
// SysV AMD64 arguments:
//   RDI: exclusive, initialized 1280-byte WidePoint (X/Y/Z/T at 0/320/640/960).
//   RSI: read-only staged fields (Y2-X2), (Y2+X2), 2*d*T2, and optionally 2*Z2.
//        Each field is five 64-byte vectors. Affine input occupies 960 bytes;
//        projective input occupies 1280 bytes, with 2*Z2 at offset 960.
//   RDX: compute_t, exactly 0 or 1. Zero writes an all-zero T coordinate.
//   RCX: affine, exactly 0 or 1. One substitutes D=2*Z1 and never reads 2*Z2.
// Both buffers are 64-byte aligned and disjoint from each other and this
// routine's writable stack frame (up to 1352 bytes below entry RSP).
// Every input limb, including T1 and the staged fields, must be < 2^52.
// No curve-membership or cached-coordinate consistency assumption is needed.
//
// A=(Y1-X1)*(Y2-X2), B=(Y1+X1)*(Y2+X2), C=T1*(2*d*T2),
// D=Z1*(2*Z2) (projective) or 2*Z1 (affine).
// E=B-A, F=D-C, G=D+C, H=B+A.
// Output: X=E*F, Y=G*H, Z=F*G, T=E*H or zero.
// Every output byte is written. Output limbs 0,2,3,4 < 2^51 and limb1 < 2^52.
//
// Clobbers RAX, RCX, R8, R9, arithmetic flags and ZMM0..31. Preserves SysV
// callee-saved registers and restores RSP. Uses 1280 bytes of aligned scratch;
// the RBP save, alignment padding and two nested calls bring maximum usage
// to 1352 bytes below entry RSP. All point inputs are read before point stores.
// Branches depend only on the two public mode flags. The helpers preserve
// RDI/RSI/RDX/R9; multiplication also preserves RCX and ZMM28/29.
.text
.p2align 4
.globl ed25519_simd_add_cached_ifma
.hidden ed25519_simd_add_cached_ifma
.type ed25519_simd_add_cached_ifma,@function

// Numeric macro arguments keep register allocation visible in the source.
.macro ca_rrr op, dst, a, b
    \op zmm\dst, zmm\a, zmm\b
.endm
.macro ca_rri op, dst, a, n
    \op zmm\dst, zmm\a, \n
.endm
.macro ca_rr op, dst, a
    \op zmm\dst, zmm\a
.endm
.macro ca_read dst, base, offset
    vmovdqu64 zmm\dst, [\base + \offset]
.endm
.macro ca_write base, offset, src
    vmovdqu64 [\base + \offset], zmm\src
.endm

.macro ca_load base, offset, first
.irp i,0,1,2,3,4
    ca_read %(\first+\i), \base, %(\offset+64*\i)
.endr
.endm
.macro ca_store base, offset, first
.irp i,0,1,2,3,4
    ca_write \base, %(\offset+64*\i), %(\first+\i)
.endr
.endm

// Carry all five limbs independently. Input limbs < 2^63; output limbs1..4
// are < 2^51 + 4096, and limb0 < 2^51 + 19*4096. These bounds suffice for
// IFMA52; a serial carry chain is unnecessary.
// ZMM20..24 are scratch; 28=19, 29=2^51-1.
.macro ca_reduce first
.irp i,0,1,2,3,4
    ca_rri vpsrlq, %(20+\i), %(\first+\i), 51
    ca_rrr vpandq, %(\first+\i), %(\first+\i), 29
.endr
.irp i,0,1,2,3
    ca_rrr vpaddq, %(\first+\i+1), %(\first+\i+1), %(20+\i)
.endr
    vpmullq zmm24, zmm24, zmm28
    vpaddq zmm\first, zmm\first, zmm24
.endm

.altmacro
ed25519_simd_add_cached_ifma:
    push rbp
    mov rbp, rsp
    and rsp, -64
    sub rsp, 1280
    mov r9, rsp
    mov eax, 19
    vpbroadcastq zmm28, rax
    mov rax, 0x7ffffffffffff
    vpbroadcastq zmm29, rax
    // Limbwise 2048*p covers the independent kernel's loose limb0 < 2^60
    // as well as 52-bit inputs. Subtractions do not underflow, and every
    // sum stays below 2^63 before ca_reduce restores the IFMA52 bound.
    mov rax, 0x3fffffffffff6800
    vpbroadcastq zmm30, rax
    mov rax, 0x3ffffffffffff800
    vpbroadcastq zmm31, rax

    ca_load rdi, 0, 0
    ca_load rdi, 320, 5
.irp i,0,1,2,3,4
    ca_rrr vpaddq, %(10+\i), %(5+\i), \i
.if \i == 0
    ca_rrr vpaddq, %(5+\i), %(5+\i), 30
.else
    ca_rrr vpaddq, %(5+\i), %(5+\i), 31
.endif
    ca_rrr vpsubq, \i, %(5+\i), \i
.endr
    ca_reduce 0
    ca_reduce 10
    // Pair A and B despite their different cached right operands. Keep the
    // sum in registers, avoiding a temporary store/reload of all five limbs.
.irp i,0,1,2,3,4
    ca_rr vmovdqa64, %(5+\i), %(10+\i)
.endr
    lea r8, [rsi + 0]
    call .Lca_multiply_independent
    ca_store r9, 0, 5          // A
    ca_store r9, 320, 0        // B

    ca_load rdi, 960, 0
    lea r8, [rsi + 640]
    call .Lca_compute_c_d      // C in 5..9, D in 0..4

.irp i,0,1,2,3,4
    ca_rrr vpaddq, %(10+\i), \i, %(5+\i)  // G=D+C
.if \i == 0
    ca_rrr vpaddq, \i, \i, 30
.else
    ca_rrr vpaddq, \i, \i, 31
.endif
    ca_rrr vpsubq, \i, \i, %(5+\i)       // F=D+2048*p-C
.endr
    ca_reduce 0
    ca_reduce 10
    ca_store r9, 640, 0        // F
    ca_store r9, 960, 10       // G

    ca_load r9, 320, 0         // B
    ca_load r9, 0, 5           // A
.irp i,0,1,2,3,4
    ca_rrr vpaddq, %(10+\i), \i, %(5+\i)  // H=B+A
.if \i == 0
    ca_rrr vpaddq, \i, \i, 30
.else
    ca_rrr vpaddq, \i, \i, 31
.endif
    ca_rrr vpsubq, \i, \i, %(5+\i)       // E=B+2048*p-A
.endr
    ca_reduce 0
    ca_reduce 10
    ca_store r9, 0, 0          // E
    ca_store r9, 320, 10       // H

    // Pair X=E*F with Z=G*F, then Y=G*H with optional T=E*H.
    ca_load r9, 960, 5
    lea r8, [rsp + 640]
    call .Lca_multiply_pair
    ca_store rdi, 0, 0
    ca_store rdi, 640, 5
    ca_load r9, 960, 0
    lea r8, [rsp + 320]
    call .Lca_compute_y_t
    ca_store rdi, 320, 0
    ca_store rdi, 960, 5
    mov rsp, rbp
    pop rbp
    vzeroupper
    ret

.Lca_compute_c_d:
    dec ecx
    jne .Lca_projective_d
    call .Lca_multiply_single
.irp i,0,1,2,3,4
    ca_rr vmovdqa64, %(5+\i), \i
.endr
    ca_load rdi, 640, 0
.irp i,0,1,2,3,4
    ca_rrr vpaddq, \i, \i, \i
.endr
    ret
.Lca_projective_d:
    ca_load rdi, 640, 5
    // The independent kernel returns its second product first: D, then C.
    call .Lca_multiply_independent
    ret

.Lca_compute_y_t:
    mov rcx, rdx
    dec ecx
    jne .Lca_without_t
    ca_load r9, 0, 5
    call .Lca_multiply_pair
    ret
.Lca_without_t:
    call .Lca_multiply_single
.irp i,5,6,7,8,9
    ca_rrr vpxorq, \i, \i, \i
.endr
    ret

// ZMM0..4 and (for a pair) 5..9 are left operands. Accumulate exact columns
// as lo+2^52*hi, folding degree >=5 by 19. ZMM10..19 hold output limbs until
// all source limbs have been consumed. Interleave both products' low/high
// accumulators in ZMM20/21 and ZMM22/23: four independent IFMA chains.
//
// The independent kernel reads different right operands at R8 and R8+320.
// Both use memory operands to avoid spilling live inputs or partial outputs.
// It returns product 1 in ZMM0..4 and product 0 in ZMM5..9. Limb0 is < 2^60
// and limbs1..4 are < 2^51: the following additions and ca_reduce normalize
// them, so carrying limb0 here would be redundant. This kernel is used only
// for A/B and projective C/D, never for the final point coordinates.
// With 52-bit inputs, the last carry is < 10*2^52+128; folding it by 19
// gives limb0 < 191*2^52 < 2^60. The 2048*p subtraction bias covers it.
//
// Single and shared-RHS pair return strict products in the original order.
// Single caches the right operand in ZMM5..9, with carry in ZMM24. Shared-RHS
// pair caches right limbs0..4 in ZMM24/26/27/30/31. In both paired kernels,
// the second product's carry is in ZMM25; the first after columns0..3 uses
// ZMM16..19: each is a future second-product output, read before that output
// is written. Column4 puts the final carry in ZMM24, after right limb0's
// last use. Each shared right limb needs only one load per kernel call.
.macro ca_memterm op, dst, lhs, offset
    \op zmm\dst, zmm\lhs, [r8 + \offset]
.endm
.macro ca_term i, streams, right
.irp high,0,1
.irp s,0,1
.if \s < \streams
.if \high
    ca_rrr vpmadd52huq, %(21+2*\s), %(5*\s+\i), \right
.else
    ca_rrr vpmadd52luq, %(20+2*\s), %(5*\s+\i), \right
.endif
.endif
.endr
.endr
.endm

.macro ca_column k, streams, independent=0
.irp s,0,1
.if \s < \streams
    ca_rrr vpxorq, %(20+2*\s), %(20+2*\s), %(20+2*\s)
    ca_rrr vpxorq, %(21+2*\s), %(21+2*\s), %(21+2*\s)
.endif
.endr
.irp wrapped,1,0
.irp i,0,1,2,3,4
.irp j,0,1,2,3,4
.if \i+\j == \k+5*\wrapped
.if \independent
.irp high,0,1
.irp stream,0,1
.if \high
    ca_memterm vpmadd52huq, %(21+2*\stream), %(5*\stream+\i), %(64*\j + 320*\stream)
.else
    ca_memterm vpmadd52luq, %(20+2*\stream), %(5*\stream+\i), %(64*\j + 320*\stream)
.endif
.endr
.endr
.elseif \streams == 1
    ca_term \i, 1, %(5+\j)
.elseif \j == 0
    ca_term \i, \streams, 24
.elseif \j < 3
    ca_term \i, \streams, %(25+\j)
.else
    ca_term \i, \streams, %(27+\j)
.endif
.endif
.endr
.endr
.if \wrapped && (\k < 4)
.irp s,0,1
.if \s < \streams
    ca_rrr vpmullq, %(20+2*\s), %(20+2*\s), 28
    ca_rrr vpmullq, %(21+2*\s), %(21+2*\s), 28
.endif
.endr
.endif
.endr
.irp s,0,1
.if \s < \streams
.if \k
.if (\streams == 2) && (\s == 0)
    // Consume the first product's carry before the second writes this slot.
    ca_rrr vpaddq, 20, 20, %(15+\k)
.else
    ca_rrr vpaddq, %(20+2*\s), %(20+2*\s), %(24+\s)
.endif
.endif
    ca_rrr vpandq, %(10+5*\s+\k), %(20+2*\s), 29
.if (\streams == 2) && (\s == 0) && (\k < 4)
    // Borrow the second product's next output slot; keep right limb0 live.
    ca_rri vpsrlq, %(16+\k), 20, 51
    ca_rri vpsllq, 21, 21, 1
    ca_rrr vpaddq, %(16+\k), %(16+\k), 21
.else
    ca_rri vpsrlq, %(24+\s), %(20+2*\s), 51
    ca_rri vpsllq, %(21+2*\s), %(21+2*\s), 1
    ca_rrr vpaddq, %(24+\s), %(24+\s), %(21+2*\s)
.endif
.endif
.endr
.endm

.macro ca_multiply_kernel streams, independent=0
.if !\independent
.if \streams == 1
    ca_load r8, 0, 5
.else
    vmovdqu64 zmm24, [r8]
    vmovdqu64 zmm26, [r8 + 64]
    vmovdqu64 zmm27, [r8 + 128]
    vmovdqu64 zmm30, [r8 + 192]
    vmovdqu64 zmm31, [r8 + 256]
.endif
.endif
.irp k,0,1,2,3,4
    ca_column \k, \streams, \independent
.endr
.irp s,0,1
.if \s < \streams
    ca_rrr vpmullq, %(24+\s), %(24+\s), 28
    ca_rrr vpaddq, %(10+5*\s), %(10+5*\s), %(24+\s)
.if \independent
    ca_rr vmovdqa64, %(5*(1-\s)), %(10+5*\s)
    ca_rr vmovdqa64, %(5*(1-\s)+1), %(10+5*\s+1)
.else
    ca_rri vpsrlq, %(24+\s), %(10+5*\s), 51
    ca_rrr vpandq, %(5*\s), %(10+5*\s), 29
    ca_rrr vpaddq, %(5*\s+1), %(10+5*\s+1), %(24+\s)
.endif
.irp i,2,3,4
.if \independent
    ca_rr vmovdqa64, %(5*(1-\s)+\i), %(10+5*\s+\i)
.else
    ca_rr vmovdqa64, %(5*\s+\i), %(10+5*\s+\i)
.endif
.endr
.endif
.endr
    ret
.endm

.Lca_multiply_independent:
    ca_multiply_kernel 2, 1
.Lca_multiply_pair:
    ca_multiply_kernel 2
.Lca_multiply_single:
    ca_multiply_kernel 1
.noaltmacro
.size ed25519_simd_add_cached_ifma, .-ed25519_simd_add_cached_ifma
.purgem ca_load
.purgem ca_store
.purgem ca_reduce
.purgem ca_memterm
.purgem ca_term
.purgem ca_column
.purgem ca_multiply_kernel
.purgem ca_rrr
.purgem ca_rri
.purgem ca_rr
.purgem ca_read
.purgem ca_write
