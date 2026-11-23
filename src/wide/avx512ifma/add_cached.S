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
// X1 and Y1 may contain folded columns below 300*2^52. Limbs of Z1,
// T1 and the staged fields must be below 2^52.
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
    vpmadd52luq zmm\first, zmm24, zmm28
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
    // Each folded product column is below 300*2^52. The 2048*p bias
    // covers subtraction before the first carry, and the resulting sums
    // fit below 2^63. ca_reduce restores the IFMA52 input bound.
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
    call .Lca_multiply_single_raw
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
    call .Lca_multiply_single_raw
    // Y leaves the routine. The other single product, affine C, feeds D±C.
    fe51_carry 0, 0, ca_rrr, ca_rri
.irp i,5,6,7,8,9
    ca_rrr vpxorq, \i, \i, \i
.endr
    ret

// Independent right operands are 320 bytes apart. Keep the second product
// in its consumed right operand while the first uses the freed registers.
// Return B/D in 0..4 and A/C in 5..9, as needed by the point formulas.
.Lca_multiply_independent:
    ca_load r8, 320, 22
    fe51_product 5, 22, 22, ca_rrr, ca_rri, 1
    ca_load r8, 0, 5
    fe51_product 0, 5, 5, ca_rrr, ca_rri, 1
.irp i,0,1,2,3,4
    ca_rr vmovdqa64, \i, %(22+\i)
.endr
    ret
.Lca_multiply_pair:
    ca_load r8, 0, 22
    fe51_product 0, 22, 0, ca_rrr, ca_rri, 1
    fe51_carry 0, 0, ca_rrr, ca_rri
    fe51_product 5, 22, 5, ca_rrr, ca_rri
    ret
.Lca_multiply_single_raw:
    ca_load r8, 0, 22
    fe51_product 0, 22, 0, ca_rrr, ca_rri, 1
    ret
.noaltmacro
.size ed25519_simd_add_cached_ifma, .-ed25519_simd_add_cached_ifma
.purgem ca_load
.purgem ca_store
.purgem ca_reduce
.purgem fe51_product
.purgem fe51_carry
.purgem ca_rrr
.purgem ca_rri
.purgem ca_rr
.purgem ca_read
.purgem ca_write
