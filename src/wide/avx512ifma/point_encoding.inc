// Private convention shared by the point decoder and recompressor.
// ZMM0..4 hold one eight-lane field. All field pointers are 64-byte aligned.
// decompress_r.S emits the shared kernels inside its certified symbol extent.
// .Lfe51_mul multiplies by [R8]; .Lfe51_mul_strict additionally tightens
// limbs 0, 2 and 4 for .Lfe51_square_strict. All three preserve general
// registers, opmask registers and the field constants in ZMM28..31.
.macro fe51_load base, off
.irp i,0,1,2,3,4
    vmovdqa64 zmm\i, [\base + \off + 64*\i]
.endr
.endm
.macro fe51_store base, off
.irp i,0,1,2,3,4
    vmovdqa64 [\base + \off + 64*\i], zmm\i
.endr
.endm
.macro fe51_constants
    vpbroadcastq zmm28, qword ptr [rip + .Ltor_modulus_fold]
    vpbroadcastq zmm29, qword ptr [rip + .Ltor_limb_mask]
    vpbroadcastq zmm30, qword ptr [rip + .Ltor_bias0]
    vpbroadcastq zmm31, qword ptr [rip + .Ltor_bias1]
.endm

// Return little-endian words 0..3 in ZMM0,4,2,6; clobber ZMM1,3,5,7..9.
.macro encoded_point_words base
    // Transpose four unaligned cache lines into the four 64-bit words
    // of each encoding. The input ends at byte 255.
    vmovdqu64 zmm0, [\base]
    vmovdqu64 zmm1, [\base + 64]
    vmovdqu64 zmm2, [\base + 128]
    vmovdqu64 zmm3, [\base + 192]
    vshufi64x2 zmm4, zmm0, zmm1, 0x88
    vshufi64x2 zmm5, zmm2, zmm3, 0x88
    vshufi64x2 zmm6, zmm0, zmm1, 0xdd
    vshufi64x2 zmm7, zmm2, zmm3, 0xdd
    vmovdqa64 zmm8, [rip + .Lencoding_even]
    vmovdqa64 zmm9, [rip + .Lencoding_odd]
    vmovdqa64 zmm0, zmm4
    vpermt2q zmm0, zmm8, zmm5
    vpermt2q zmm4, zmm9, zmm5
    vmovdqa64 zmm2, zmm6
    vpermt2q zmm2, zmm8, zmm7
    vpermt2q zmm6, zmm9, zmm7
.endm

// Split the low 255 bits of encoded_point_words into five radix-51 limbs.
.macro encoded_y_limbs
    vpsrlq zmm1, zmm0, 51
    vpsllq zmm5, zmm4, 13
    vporq zmm1, zmm1, zmm5
    vpsrlq zmm4, zmm4, 38
    vpsllq zmm5, zmm2, 26
    vporq zmm4, zmm4, zmm5
    vpsrlq zmm3, zmm2, 25
    vpsllq zmm5, zmm6, 39
    vporq zmm3, zmm3, zmm5
    vpandq zmm2, zmm4, zmm29
    vpsrlq zmm4, zmm6, 12
.irp i,0,1,3,4
    vpandq zmm\i, zmm\i, zmm29
.endr
.endm

// Each limb is less than 2*radix-20. In this range a high digit with
// all 51 low bits set must equal radix-1.
.macro fe51_high_ones
    vpandq zmm10, zmm1, zmm2
    vpandq zmm11, zmm3, zmm4
    vpandq zmm10, zmm10, zmm11
    vpcmpeqq k1, zmm10, zmm29
.endm

// K1 receives the lanes with ZMM0..4 times Z equal to the selected
// projective coordinate modulo p. Each input limb fits in 52 bits.
.macro fe51_match_coordinate point, coordinate
.irp i,5,6,7,8,9
    vmovdqa64 zmm\i, [\point + 640 + 64*(\i-5)]
.endr
    // Seed the product with 1024*p minus the coordinate. Every limb stays positive for
    // 52-bit inputs. The parallel carry leaves a representative in (0,2*p),
    // so equality holds exactly when its five digits equal p.
    vpsubq zmm10, zmm30, [\point + \coordinate]
.irp i,11,12,13,14
    vpsubq zmm\i, zmm31, [\point + \coordinate + 64*(\i-10)]
.endr
    call .Ltor_seeded_columns
    call .Lfe51_carry
    fe51_high_ones
    vpcmpeqq k1{k1}, zmm0, qword ptr [rip + .Lfe51_p0]{1to8}
.endm

.macro fe51_match_projective_y point
    fe51_match_coordinate \point, 320
.endm

.macro fe51_squares n
.if \n == 1
    call .Lfe51_square_strict
.else
    mov ecx, \n
.Lfe51_repeat\@:
    call .Lfe51_square_strict
    dec ecx
    jne .Lfe51_repeat\@
.endif
.endm

// A carried field product h is in [0, 2*p). The carry out of h+19 is
// exactly [h >= p], even when an individual limb still needs a carry.
.macro fe51_modulus_carry
    vpaddq zmm20, zmm0, zmm28
.irp i,1,2,3,4
    vpsrlq zmm20, zmm20, 51
    vpaddq zmm20, zmm20, zmm\i
.endr
    vpsrlq zmm20, zmm20, 51
.endm
