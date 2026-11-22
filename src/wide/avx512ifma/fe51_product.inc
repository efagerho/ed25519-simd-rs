// Multiply five-limb radix-2^51 fields with limbs below 2^52. For degree k,
// sum the high and low 52-bit halves of products with i+j=k into H[k] and L[k].
// Since 2^52 is twice the radix, column k is L[k]+2*H[k-1]. Keep H[k] in
// register 13+k, then reuse 12+k for column k. Fold columns 5..9 by 19.
// ZMM12..21 are scratch, ZMM28 holds 19, and ZMM29 holds 2^51-1. Output
// may alias either operand. The caller supplies its numeric register macros.
.macro fe51_product left, right, dst, rrr, rri, raw_columns=0
.irp k,0,1,2,3,4,5,6,7,8
    \rrr vpxorq, %(13+\k), %(13+\k), %(13+\k)
.irp i,0,1,2,3,4
.if (\k >= \i) && (\k-\i <= 4)
    \rrr vpmadd52huq, %(13+\k), %(\left+\i), %(\right+\k-\i)
.endif
.endr
.endr
    vpxorq zmm12, zmm12, zmm12
.irp k,0,1,2,3,4,5,6,7,8,9
.if \k
    \rri vpsllq, %(12+\k), %(12+\k), 1
.endif
.irp i,0,1,2,3,4
.if (\k >= \i) && (\k-\i <= 4)
    \rrr vpmadd52luq, %(12+\k), %(\left+\i), %(\right+\k-\i)
.endif
.endr
.endr
.irp k,0,1,2,3,4
    \rrr vpmullq, %(17+\k), %(17+\k), 28
.if \raw_columns
    // Return folded columns. The caller carries them, possibly after
    // a sum or difference, before using them as IFMA inputs.
    \rrr vpaddq, %(\dst+\k), %(12+\k), %(17+\k)
.else
    \rrr vpaddq, %(12+\k), %(12+\k), %(17+\k)
.endif
.endr
.if !\raw_columns
    // Each folded column is below 5*3*20*2^52. Start with limb one
    // so only that output can exceed 51 bits. The final carry times 19
    // fits below 2^52, allowing an exact low-half IFMA into limb zero.
.irp k,1,2,3,4
    \rri vpsrlq, 17, %(12+\k), 51
    \rrr vpandq, %(\dst+\k), %(12+\k), 29
.if \k < 4
    \rrr vpaddq, %(13+\k), %(13+\k), 17
.endif
.endr
    vpmadd52luq zmm12, zmm17, zmm28
    vpsrlq zmm17, zmm12, 51
    \rrr vpandq, \dst, 12, 29
    \rrr vpaddq, %(\dst+1), %(\dst+1), 17
.endif
.endm
