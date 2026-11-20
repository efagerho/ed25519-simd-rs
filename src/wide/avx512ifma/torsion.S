// ZIP-215 equation check, eight independent lanes. SysV RDI=P, RSI=affine R,
// both read-only WidePoints (possibly identical). R.z is implicit. The field
// inputs have five radix-2^51 limbs below 2^52. EAX returns the lane bitmask.
// For valid extended coordinates, bit j says [8](P[j]-R[j]) is the identity.
// X/Y/Z/T begin at byte offsets 0/320/640/960. The nested call uses at
// most 1032 stack bytes below entry RSP including alignment and saved RBP.
// All writes are private to the stack. This routine is not formally verified.
.text
.p2align 4
.globl ed25519_simd_check_8_torsion_ifma
.hidden ed25519_simd_check_8_torsion_ifma
.type ed25519_simd_check_8_torsion_ifma,@function
.altmacro

.macro tor_op op, d, a, b
    \op zmm\d, zmm\a, zmm\b
.endm
.macro tor_memop op, reg, base, disp
    \op zmm\reg, zmm\reg, [\base + \disp]
.endm
.macro tor_broadcast d, table, j
    vpbroadcastq zmm\d, qword ptr [rip + \table + 8*\j]
.endm
.macro tor_mem op, reg, base, disp
.ifc \op,load
    vmovdqu64 zmm\reg, [\base + \disp]
.else
    vmovdqu64 [\base + \disp], zmm\reg
.endif
.endm
.macro tor_field op, first, base, disp
.irp j,0,1,2,3,4
    tor_mem \op, %(\first+\j), \base, %(\disp+64*\j)
.endr
.endm

// Carry the five columns independently. Folding the top carry by 19 is
// exact for inputs below 2^63. Each carried limb is below 2^51+2^17.
.macro tor_carry_limb reg, carry
    vpsrlq zmm\carry, zmm\reg, 51
    vpandq zmm\reg, zmm\reg, zmm29
.endm
.macro tor_carry first
.irp j,0,1,2,3,4
    tor_carry_limb %(\first+\j), %(10+\j)
.endr
.irp j,1,2,3,4
    tor_op vpaddq, %(\first+\j), %(\first+\j), %(9+\j)
.endr
    vpmadd52luq zmm\first, zmm14, zmm28
.endm

// Multiply five 52-bit limbs by a small scalar. Seed each low IFMA with
// twice the previous high half, or 38 times the top half for limb zero.
// Each output is below 2^52 + 38*121666; sumdiff carries before reuse.
.macro tor_scale first, out, factor
.irp j,0,1,2,3,4
    tor_op vpxorq, %(10+\j), %(10+\j), %(10+\j)
    tor_op vpmadd52huq, %(10+\j), %(\first+\j), \factor
.endr
    tor_op vpmullq, \out, 14, 24
.irp j,1,2,3,4
    tor_op vpaddq, %(\out+\j), %(9+\j), %(9+\j)
.endr
.irp j,0,1,2,3,4
    tor_op vpmadd52luq, %(\out+\j), %(\first+\j), \factor
.endr
.endm

// (a,b) -> (a+b,a-b) in fields 0..4 and 5..9, biasing the difference by 1024*p.
.macro tor_sumdiff
.irp j,0,1,2,3,4
.if \j == 0
    tor_op vpaddq, 10, 0, 30
.else
    tor_op vpaddq, 10, \j, 31
.endif
    tor_op vpaddq, \j, \j, %(5+\j)
    tor_op vpsubq, %(5+\j), 10, %(5+\j)
.endr
    tor_carry 0
    tor_carry 5
.endm

// With B=2^51, the carried inputs here represent positive integers below
// 2*p. Only p represents zero. Adding 18 to limb zero makes all five
// digits of p equal B-1. Each adjusted digit is below 2*B-1, so the
// residue B-1 mod B uniquely determines it, including for loose limbs.
// Their bitwise AND tests all five digits at once.
.macro tor_zero mask, a,b,c,d,e
    vpaddq zmm10, \a, zmm27
    vpandq zmm11, \b, \c
    vpandq zmm12, \d, \e
    vpandq zmm10, zmm10, zmm11
    vpandq zmm10, zmm10, zmm12
    vpcmpeqq \mask, zmm10, zmm29
.endm

.macro tor_mul
    call .Ltor_columns
    tor_carry 0
.endm

ed25519_simd_check_8_torsion_ifma:
    push rbp
    mov rbp, rsp
    vpbroadcastq zmm28, qword ptr [rip + .Ltor_modulus_fold]
    vpbroadcastq zmm29, qword ptr [rip + .Ltor_limb_mask]
    vpbroadcastq zmm30, qword ptr [rip + .Ltor_bias0]
    vpbroadcastq zmm31, qword ptr [rip + .Ltor_bias1]

    // E=X*y-Y*x. This is half of B-A in the mixed subtraction formula.
    tor_field load, 0, rdi, 320
    tor_field load, 5, rsi, 0
.irp j,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27
    tor_op vpxorq, \j, \j, \j
.endr
    call .Ltor_convolve             // polynomial Y*x
    // Negate the low and high columns modulo 2^64, with a 1024*p bias
    // in the low columns. Folding is linear. Each unbiased folded column
    // is below 300*2^52, so bias + col(X*y) - col(Y*x) is in (0,2^62).
    // Its low 64 bits are therefore the exact input to the unsigned carry.
    vpxorq zmm0, zmm0, zmm0
    vpsubq zmm10, zmm30, zmm10
.irp j,11,12,13,14
    tor_op vpsubq, \j, 31, \j
.endr
.irp j,15,16,17,18,19,20,21,22,23,24,25,26,27
    tor_op vpsubq, \j, 0, \j
.endr
    tor_field load, 0, rdi, 0
    tor_field load, 5, rsi, 320
    call .Ltor_add_product          // 1024*p + X*y - Y*x
    tor_carry 0
    vpbroadcastq zmm27, qword ptr [rip + .Ltor_zero_adjust]
    tor_zero k1, zmm0,zmm1,zmm2,zmm3,zmm4
    kmovw eax, k1
    // Xq is a multiple of E. All eight lanes must have E=0 to return
    // here; this branch depends only on public verification inputs.
    cmp eax, 255
    je .Ltor_return
    // Only the full check spills three aligned 320-byte scratch fields.
    and rsp, -64
    sub rsp, 960
    tor_field store, 0, rsp, 320
    // H=(Y-X)*(y+x)+E = Y*y-X*x, half of B+A.
    tor_field load, 0, rdi, 320
    tor_field load, 5, rsi, 320
.irp j,0,1,2,3,4
.if \j == 0
    tor_op vpaddq, 0, 0, 30
.else
    tor_op vpaddq, \j, \j, 31
.endif
    tor_memop vpsubq, \j, rdi, %(64*\j)
    tor_memop vpaddq, %(5+\j), rsi, %(64*\j)
.endr
    tor_carry 0
    tor_carry 5
    call .Ltor_columns
.irp j,0,1,2,3,4
    tor_memop vpaddq, \j, rsp, %(320+64*\j)
.endr
    tor_carry 0
    tor_field store, 0, rsp, 0

    tor_field load, 0, rdi, 960
    tor_field load, 5, rsi, 960
    tor_mul
    // D=2Z, C=2*d*T*t. Since d=-121665/121666, scale D+C and D-C by 121666/2.
    // The resulting Xq and Yq share a nonzero factor.
    vpbroadcastq zmm24, qword ptr [rip + .Ltor_double_fold]
    vpbroadcastq zmm25, qword ptr [rip + .Ltor_d_num]
    tor_scale 0, 5, 25              // 121665*T*t
    vpbroadcastq zmm25, qword ptr [rip + .Ltor_d_den]
    tor_field load, 15, rdi, 640
    tor_scale 15, 0, 25             // 121666*Z
    tor_sumdiff
    tor_field store, 0, rsp, 640    // scaled G=D-C
    tor_field load, 0, rsp, 320
    tor_mul                  // Xq=E*(scaled F)
    tor_field store, 0, rsp, 320
    tor_field load, 0, rsp, 640
    tor_field load, 5, rsp, 0
    tor_mul                  // Yq=G*H

    // The doubling numerator is proportional to Xq*Yq*(Xq^2+Yq^2). In the prime field,
    // its roots are Xq=0, Yq=0, or Xq=+/-i*Yq, where i^2=-1.
.irp j,0,1,2,3,4
    tor_broadcast %(5+\j), .Ltor_sqrt_m1, \j
.endr
    tor_mul
    tor_field load, 5, rsp, 320
    vpbroadcastq zmm27, qword ptr [rip + .Ltor_zero_adjust]
    tor_zero k3, zmm0,zmm1,zmm2,zmm3,zmm4
    tor_zero k4, zmm5,zmm6,zmm7,zmm8,zmm9
    korw k3, k3, k4
    tor_sumdiff
    tor_zero k4, zmm0,zmm1,zmm2,zmm3,zmm4
    korw k3, k3, k4
    tor_zero k4, zmm5,zmm6,zmm7,zmm8,zmm9
    korw k3, k3, k4
    kmovw eax, k3
.Ltor_return:
    mov rsp, rbp
    pop rbp
    vzeroupper
    ret

// Field multiply. Keep nine independent low and high polynomial columns
// in registers. A 52-bit high half contributes twice to the next 51-bit
// column. Fold columns 5..9 back by 19 before the parallel carry.
.p2align 4
.Ltor_columns:
    // Seed the low columns with 1024*p. After carrying, even a zero
    // product has a positive representative, so tor_zero only tests p.
    vmovdqa64 zmm10, zmm30
.irp j,11,12,13,14
    vmovdqa64 zmm\j, zmm31
.endr
.irp j,15,16,17,18,19,20,21,22,23,24,25,26,27
    tor_op vpxorq, \j, \j, \j
.endr
.Ltor_add_product:
    call .Ltor_convolve
.irp j,0,1,2,3,4
    tor_op vpaddq, \j, %(23+\j), %(23+\j)
.if \j < 4
    tor_op vpaddq, \j, \j, %(15+\j)
.endif
    tor_op vpmullq, \j, \j, 28
    tor_op vpaddq, \j, \j, %(10+\j)
.if \j > 0
    tor_op vpaddq, 5, %(18+\j), %(18+\j)
    tor_op vpaddq, \j, \j, 5
.endif
.endr
    ret

.p2align 4
.Ltor_convolve:
.irp a,0,1,2,3,4
.irp b,0,1,2,3,4
    tor_op vpmadd52luq, %(10+\a+\b), \a, %(5+\b)
    tor_op vpmadd52huq, %(19+\a+\b), \a, %(5+\b)
.endr
.endr
    ret

.p2align 3
.Ltor_modulus_fold: .quad 19
.Ltor_limb_mask: .quad 0x7ffffffffffff
.Ltor_bias0: .quad ((1 << 51) - 19) << 10
.Ltor_bias1: .quad ((1 << 51) - 1) << 10
.Ltor_zero_adjust: .quad 18
.Ltor_double_fold: .quad 38
.Ltor_d_num: .quad 121665
.Ltor_d_den: .quad 121666
.Ltor_sqrt_m1:
    .quad 1718705420411056, 234908883556509, 2233514472574048, 2117202627021982, 765476049583133
.size ed25519_simd_check_8_torsion_ifma, .-ed25519_simd_check_8_torsion_ifma
.noaltmacro
.purgem tor_mul
.purgem tor_op
.purgem tor_memop
.purgem tor_mem
.purgem tor_field
.purgem tor_broadcast
.purgem tor_carry_limb
.purgem tor_carry
.purgem tor_scale
.purgem tor_sumdiff
.purgem tor_zero
