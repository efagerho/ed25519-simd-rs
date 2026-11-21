// Raise a radix-51 field to (p-5)/8 = 2^252-3. The caller supplies
// three scratch slots, a multiplication by a slot and repeated squaring.
.macro fe51_pow22523 save, multiply, square_n
    \save 0
    // Raw input may use all 52 bits in every limb. The general product
    // establishes the tighter bounds needed for doubled square operands.
    \multiply 0
    \save 1
    \square_n 2
    \multiply 0
    \save 2
    \multiply 1
    \square_n 1
    \multiply 2
    // Current exponent is 31. Build exponents 2^k - 1.
    \save 1
    \square_n 5
    \multiply 1
    \save 1
    \square_n 10
    \multiply 1
    \save 2
    \square_n 20
    \multiply 2
    \square_n 10
    \multiply 1
    \save 1
    \square_n 50
    \multiply 1
    \save 2
    \square_n 100
    \multiply 2
    \square_n 50
    \multiply 1
    \square_n 2
    \multiply 0
.endm

// Square one eight-lane field. Limbs 0, 2 and 4 fit in 51 bits and
// can be doubled before IFMA. The carry chains restore these bounds.
.macro fe51_square x0, x1, x2, x3, x4
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
    // Keep selected low sums independent of the high sums until their
    // final additions. This avoids chaining low IFMAs after high IFMAs.
    // Degree four is L[4] + 2*(H[3] + 19*H[8]).
    vpxorq zmm26, zmm26, zmm26
    vpmadd52luq zmm26, \x1, \x3
    vpsllq zmm26, zmm26, 1
    vpmadd52luq zmm26, zmm10, \x4
    vpmadd52luq zmm26, \x2, \x2
    vpmullq zmm27, zmm21, zmm28
    vpaddq zmm27, zmm27, zmm16
    vpsllq zmm27, zmm27, 1
    vpaddq zmm26, zmm26, zmm27
    // Degree three: L[3] + 2*H[2] + 19*(L[8] + 2*H[7]).
    vpxorq zmm25, zmm25, zmm25
    vpmadd52luq zmm25, zmm10, \x3
    vpmadd52luq zmm25, \x1, zmm11
    vpsllq zmm27, zmm20, 1
    vpmadd52luq zmm27, \x4, \x4
    vpmullq zmm27, zmm27, zmm28
    vpsllq zmm15, zmm15, 1
    vpaddq zmm27, zmm27, zmm15
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
    // Build L[6] before joining 2*H[5]; H[5] is no longer needed later.
    vpxorq zmm27, zmm27, zmm27
    vpmadd52luq zmm27, zmm11, \x4
    vpmadd52luq zmm27, \x3, \x3
    vpsllq zmm18, zmm18, 1
    vpaddq zmm27, zmm27, zmm18
    vpmullq zmm27, zmm27, zmm28
    vpaddq zmm23, zmm23, zmm27
    vpxorq zmm22, zmm22, zmm22
    vpmadd52luq zmm22, \x0, \x0
    // Likewise, L[5] and 2*H[4] are independent until the fold by 19.
    vpxorq zmm27, zmm27, zmm27
    vpmadd52luq zmm27, \x1, zmm12
    vpmadd52luq zmm27, zmm11, \x3
    vpsllq zmm17, zmm17, 1
    vpaddq zmm27, zmm27, zmm17
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
