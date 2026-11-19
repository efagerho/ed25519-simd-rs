// Reduce eight independent 512-bit integers modulo the Ed25519 group order.
// Experimental assembly: not yet formally verified.
//
// SysV AMD64: RDI is a writable 320-byte output; RSI is a read-only 512-byte
// input. Both are disjoint, with no alignment requirement. Input row j holds
// word j of all eight little-endian integers. Output row j holds limb j of
// their canonical residues in radix 2^52. All output bytes are initialized.
// Clobbers RAX and ZMM0..31. No stack scratch, calls, or data-dependent flow;
// preserves RSP and every SysV callee-saved register.
//
// B=2^52, R=B^5, L=2^252+27742317777372353535851937790883648493.
// Split H=a+2^256*b with a,b<2^256 and form T=a*(R mod L)+b*(2^256*R mod L).
// One Montgomery reduction gives H mod L. Since T < R*L/8, the unreduced
// result is <9*L/8; one conditional subtraction of L makes it canonical.
// Product columns have at most ten IFMA terms and four modulus terms. A
// carry <15*B keeps every sum, including rounding by B-1, below 30*B <2^57.
.text
.p2align 4
.globl ed25519_simd_scalar_reduce_ifma
.hidden ed25519_simd_scalar_reduce_ifma
.type ed25519_simd_scalar_reduce_ifma,@function

.macro sr_rrr op, d, a, b
    \op zmm\d, zmm\a, zmm\b
.endm
.macro sr_rri op, d, a, n
    \op zmm\d, zmm\a, \n
.endm
.macro sr_const d, value
    mov rax, \value
    vpbroadcastq zmm\d, rax
.endm

// Unpack four 64-bit words to five 52-bit limbs. The shifted pieces have
// disjoint bits, so addition suffices. ZMM29 is B-1; ZMM8/9 are scratch.
.macro sr_unpack input, output
    sr_rrr vpandq, \output, \input, 29
.irp i,1,2,3
    sr_rri vpsrlq, 8, %(\input+\i-1), %(64-12*\i)
    sr_rri vpsllq, 9, %(\input+\i), %(12*\i)
    sr_rrr vpaddq, %(\output+\i), 8, 9
    sr_rrr vpandq, %(\output+\i), %(\output+\i), 29
.endr
    sr_rri vpsrlq, %(\output+4), %(\input+3), 16
.endm

// Accumulate one column of each constant multiplier into the same product.
// ZMM0..8: low halves; ZMM9..17: high halves; a=18..22, b=23..27.
.macro sr_product j, a, b
    sr_const 28, \a
    sr_const 29, \b
.irp i,0,1,2,3,4
    sr_rrr vpmadd52luq, %(\i+\j), %(18+\i), 28
    sr_rrr vpmadd52huq, %(9+\i+\j), %(18+\i), 28
    sr_rrr vpmadd52luq, %(\i+\j), %(23+\i), 29
    sr_rrr vpmadd52huq, %(9+\i+\j), %(23+\i), 29
.endr
.endm

// Add q_i*L_j to product column i+j. L3=0 needs no instructions.
.macro sr_mod_product i, j, constant
    sr_rrr vpmadd52luq, %(\i+\j), %(18+\i), \constant
    sr_rrr vpmadd52huq, %(9+\i+\j), %(18+\i), \constant
.endm

.altmacro
ed25519_simd_scalar_reduce_ifma:
.irp i,0,1,2,3,4,5,6,7
    vmovdqu64 zmm\i, [rsi + 64*\i]
.endr
    sr_const 29, 0xfffffffffffff
    sr_unpack 0, 18
    sr_unpack 4, 23
.irp i,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17
    sr_rrr vpxorq, \i, \i, \i
.endr
    // R mod L and (2^256*R) mod L, respectively, in radix 2^52.
    sr_product 0, 0xf48bd6721e6ed, 0x9f4e532df7449
    sr_product 1, 0x3bab5ac67e45a, 0xda9f725df7382
    sr_product 2, 0xfffffeb35e51b, 0xf5be65cc244cc
    sr_product 3, 0xfffffffffffff, 0xa3dceec73d217
    sr_product 4, 0x00fffffffffff, 0x0099411b7c309

    sr_const 28, 0x2631a5cf5d3ed
    sr_const 29, 0xdea2f79cd6581
    sr_const 30, 0x14def9
    sr_const 27, 0x100000000000
    sr_const 31, 0x51da312547e1b  // -L0^-1 mod B
    sr_const 26, 0xfffffffffffff
    vpxorq zmm23, zmm23, zmm23
.irp i,0,1,2,3,4
    // q_i makes the low limb zero mod B; carry into the next column.
    sr_rrr vpaddq, \i, \i, 23
    sr_rrr vpxorq, %(18+\i), %(18+\i), %(18+\i)
    sr_rrr vpmadd52luq, %(18+\i), \i, 31
    // q_i*L0 cancels the low bits exactly: the low-half carry is
    // ceil(column/B). Compute it without a dependent low IFMA.
    sr_rrr vpaddq, 24, \i, 26
    sr_rri vpsrlq, 24, 24, 52
    sr_rrr vpmadd52huq, %(9+\i), %(18+\i), 28
    sr_rrr vpaddq, 23, %(9+\i), 24
    sr_mod_product \i, 1, 29
    sr_mod_product \i, 2, 30
    sr_mod_product \i, 4, 27
.endr
.irp i,5,6,7,8
    sr_rrr vpaddq, \i, \i, 23
    sr_rri vpsrlq, 24, \i, 52
    sr_rrr vpandq, %(\i-5), \i, 26
    sr_rrr vpaddq, 23, %(9+\i), 24
.endr
    vmovdqa64 zmm4, zmm23

    // Subtract L in radix B, propagating borrow as a vector of 0/1.
    // Each signed difference is in [-B,B), so bit 63 is exactly the borrow.
    vpsubq zmm5, zmm0, zmm28
    vpsrlq zmm23, zmm5, 63
    vpsubq zmm6, zmm1, zmm29
    vpsubq zmm6, zmm6, zmm23
    vpsrlq zmm23, zmm6, 63
    vpsubq zmm7, zmm2, zmm30
    vpsubq zmm7, zmm7, zmm23
    vpsrlq zmm23, zmm7, 63
    vpsubq zmm8, zmm3, zmm23
    vpsrlq zmm23, zmm8, 63
    vpsubq zmm9, zmm4, zmm27
    vpsubq zmm9, zmm9, zmm23
    vpsrlq zmm23, zmm9, 63
    vpxorq zmm24, zmm24, zmm24
    vpsubq zmm23, zmm24, zmm23
.irp i,0,1,2,3,4
    // A borrow selects the original; otherwise select the reduced limbs.
    sr_rrr vpandq, %(5+\i), %(5+\i), 26
    sr_rrr vpxorq, \i, \i, %(5+\i)
    sr_rrr vpandq, \i, \i, 23
    sr_rrr vpxorq, \i, \i, %(5+\i)
    vmovdqu64 [rdi + 64*\i], zmm\i
.endr
    vzeroupper
    ret
.size ed25519_simd_scalar_reduce_ifma, .-ed25519_simd_scalar_reduce_ifma
.noaltmacro
.purgem sr_rrr
.purgem sr_rri
.purgem sr_const
.purgem sr_unpack
.purgem sr_product
.purgem sr_mod_product
