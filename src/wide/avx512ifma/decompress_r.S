// Deferred ZIP-215 R decoding. SysV AMD64: RDI receives one or two aligned
// 1280-byte WidePoints; RSI points to that many unaligned 256-byte chunks
// of eight compressed points; RDX is the chunk count (1 or 2).
// EAX returns one mask byte per chunk, bit j for lane j. Both signs of x=0
// and noncanonical y are allowed.
// Input bytes must be disjoint from the output. All four coordinates
// are written with limbs below 2^52. Z is one; on valid lanes T equals X*Y
// modulo p. The largest call path uses 2672 bytes below SysV entry RSP.
//
// Uses the IFMA product and curve constants in torsion.S and the squaring
// kernel and addition chain in pow22523.inc. A local field is five qword vectors in ZMM0..4.
// ZMM28=19, ZMM29=2^51-1. ZMM30..31 hold the limb biases for 1024*p.
.pushsection .text.ed25519_simd_zip215_decode_r,"ax",@progbits
.altmacro
.macro zr_load base, off
.irp i,0,1,2,3,4
    vmovdqa64 zmm\i, [\base + \off + 64*\i]
.endr
.endm
.macro zr_store base, off
.irp i,0,1,2,3,4
    vmovdqa64 [\base + \off + 64*\i], zmm\i
.endr
.endm
.macro zr_constants
    vpbroadcastq zmm28, qword ptr [rip + .Ltor_modulus_fold]
    vpbroadcastq zmm29, qword ptr [rip + .Ltor_limb_mask]
    vpbroadcastq zmm30, qword ptr [rip + .Ltor_bias0]
    vpbroadcastq zmm31, qword ptr [rip + .Ltor_bias1]
.endm

.p2align 4
.globl ed25519_simd_zip215_decode_r
.hidden ed25519_simd_zip215_decode_r
.type ed25519_simd_zip215_decode_r,@function
ed25519_simd_zip215_decode_r:
    push rbp
    mov rbp, rsp
    push rbx
    push r12
    push r13
    push r14
    and rsp, -64
    sub rsp, 640                    // two powers or two single-chain scratch slots
    mov rbx, rdi
    mov r12d, edx
    zr_constants
    call .Lzr_setup
    mov r13d, eax
    cmp r12d, 2
    jne .Lzr_tail
    lea rdi, [rbx + 1280]
    add rsi, 256
    call .Lzr_setup
    mov r14d, eax
    lea rdx, [rbx + 1280 + 960]
    lea rsi, [rbx + 960]
    mov rdi, rsp
    call ed25519_simd_pow2_ifma
    zr_constants
    jmp .Lzr_have_power
.Lzr_tail:
    mov rsi, rsp
    call .Lzr_power_single
.Lzr_have_power:
    mov rdi, rbx
    mov rsi, rsp
    mov r9d, r13d
    call .Lzr_finish
    cmp r12d, 2
    jne .Lzr_return
    mov r13d, eax
    lea rdi, [rbx + 1280]
    lea rsi, [rsp + 320]
    mov r9d, r14d
    call .Lzr_finish
    shl eax, 8
    or eax, r13d
.Lzr_return:
    lea rsp, [rbp - 32]
    pop r14
    pop r13
    pop r12
    pop rbx
    pop rbp
    vzeroupper
    ret

.macro zr_scale_limb input, lo, hi
    vpxorq zmm\hi, zmm\hi, zmm\hi
    vpmadd52huq zmm\hi, zmm\input, zmm26
    vpmullq zmm\lo, zmm\input, zmm25
    vpandq zmm\lo, zmm\lo, zmm29
.endm
.macro zr_scaled_uv i, lo, carry
.if \i
    vpaddq zmm\lo, zmm\lo, zmm\carry
    vpaddq zmm\i, zmm\i, zmm31
.else
    vpaddq zmm\i, zmm\i, zmm30
.endif
    vmovdqa64 [rdi + 64*\i], zmm\lo
    vpsubq zmm\i, zmm\i, zmm\lo
.endm

.Lzr_setup:
    // Transpose four unaligned cache lines into the four 64-bit words
    // of each encoding. The input ends at byte 255.
    vmovdqu64 zmm0, [rsi]
    vmovdqu64 zmm1, [rsi + 64]
    vmovdqu64 zmm2, [rsi + 128]
    vmovdqu64 zmm3, [rsi + 192]
    vshufi64x2 zmm4, zmm0, zmm1, 0x88
    vshufi64x2 zmm5, zmm2, zmm3, 0x88
    vshufi64x2 zmm6, zmm0, zmm1, 0xdd
    vshufi64x2 zmm7, zmm2, zmm3, 0xdd
    vmovdqa64 zmm8, [rip + .Lzr_even]
    vmovdqa64 zmm9, [rip + .Lzr_odd]
    vmovdqa64 zmm0, zmm4
    vpermt2q zmm0, zmm8, zmm5
    vpermt2q zmm4, zmm9, zmm5
    vmovdqa64 zmm2, zmm6
    vpermt2q zmm2, zmm8, zmm7
    vpermt2q zmm6, zmm9, zmm7
    vpmovq2m k2, zmm6
    kmovw eax, k2
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
    zr_store rdi, 320               // keep the decoded y
    lea r8, [rdi + 320]
    call .Lzr_mul_memory            // yy = y*y, in a positive representation
    // Scale both numerator and denominator by 121666. Then u=121666*(yy-1)
    // and v=yy-u because d=-121665/121666. The 1024*p product bias in
    // yy gives limb zero a positive folded carry, so yy[0]-1 cannot borrow.
    // For an input limb h, high52(h * (2*121666)) is its radix-51 carry.
    vpbroadcastq zmm25, qword ptr [rip + .Ltor_d_den]
    vpaddq zmm26, zmm25, zmm25
    vpsubq zmm5, zmm0, qword ptr [rip + .Lzr_one]{1to8}
    zr_scale_limb 5, 10, 15
.irp i,1,2,3,4
    zr_scale_limb \i, %(10+\i), %(15+\i)
.endr
    vpmadd52luq zmm10, zmm19, zmm28
.irp i,0,1,2,3,4
    zr_scaled_uv \i, %(10+\i), %(14+\i)
.endr
    call .Lzr_reduce
    zr_store rdi, 640
    zr_load rdi, 0
    lea r8, [rdi + 640]
    call .Lzr_mul_memory
    zr_store rdi, 960               // uv for the exponentiation
    ret

// Each limb is less than 2*radix-20. In this range a high digit with
// all 51 low bits set must equal radix-1.
.macro zr_high_ones
    vpandq zmm10, zmm1, zmm2
    vpandq zmm11, zmm3, zmm4
    vpandq zmm10, zmm10, zmm11
    vpcmpeqq k1, zmm10, zmm29
.endm

// RDI holds (u,y,v,uv), RSI the pow2 output, R9D the eight encoded signs.
.Lzr_finish:
    zr_load rsi, 0
    call .Lzr_square_strict
    lea r8, [rdi + 960]
    call .Lzr_mul_memory            // q = (uv)*pow^2
    // For x=u*pow we have v*x^2 = u*q. Accept q=1 directly, or q=-1
    // after multiplying x by sqrt(-1). If u=0, x=0 is always valid.
    // The biased, carried product lies between 1 and 2*p-1, exclusively:
    // residues +1 and -1 are exactly the five digits of p+1 and p-1.
    zr_high_ones
    vpcmpeqq k3{k1}, zmm0, qword ptr [rip + .Lzr_p0_plus_one]{1to8}
    vpcmpeqq k4{k1}, zmm0, qword ptr [rip + .Lzr_p0_minus_one]{1to8}
    // If y^2=1 the biased yy equals p+1. Scaling yy-1 then carries
    // 121666*p to p, so the same high-digit test detects u=0.
    zr_load rdi, 0
    zr_high_ones
    vpcmpeqq k2{k1}, zmm0, qword ptr [rip + .Lzr_p0]{1to8}
    korw k3, k3, k2                 // u=0 also gives a primary root
    korw k2, k3, k4
    kmovw r10d, k2
    mov r8, rsi
    call .Lzr_mul_memory            // x = u*pow
    zr_store rdi, 960
    call .Lzr_mul_sqrt_m1
    knotw k4, k4
.irp i,0,1,2,3,4
    vmovdqa64 zmm\i{k4}, [rdi + 960 + 64*\i]
.endr
    // x is below 2*p. The carry out of x+19 indicates x >= p;
    // subtracting the odd modulus flips parity exactly in those lanes.
    vpaddq zmm20, zmm0, zmm28
.irp i,1,2,3,4
    vpsrlq zmm20, zmm20, 51
    vpaddq zmm20, zmm20, zmm\i
.endr
    vpsrlq zmm20, zmm20, 51
    vpxorq zmm20, zmm0, zmm20
    vptestmq k3, zmm20, qword ptr [rip + .Lzr_one]{1to8}
    kmovw k4, r9d
    kxorw k3, k3, k4
    // Negate using 2*p so each limb subtraction is nonnegative, including
    // when x[0] > 2^51-19. Each limb of 2*p-x still fits in 52 bits,
    // the input bound for both X*Y and the torsion check.
    vpbroadcastq zmm20, qword ptr [rip + .Lzr_twice_p0]
    vpaddq zmm21, zmm29, zmm29
    vpsubq zmm0{k3}, zmm20, zmm0
.irp i,1,2,3,4
    vpsubq zmm\i{k3}, zmm21, zmm\i
.endr
    zr_store rdi, 0
    lea r8, [rdi + 320]
    call .Lzr_mul_memory
    zr_store rdi, 960               // T = X*Y
    vpbroadcastq zmm0, qword ptr [rip + .Lzr_one]
    vmovdqa64 [rdi + 640], zmm0
    vpxorq zmm10, zmm10, zmm10
.irp i,1,2,3,4
    vmovdqa64 [rdi + 640 + 64*\i], zmm10
.endr
    mov eax, r10d
    ret

.Lzr_square_strict:
    fe51_square zmm0, zmm1, zmm2, zmm3, zmm4
    ret
.macro zr_squares n
.if \n == 1
    call .Lzr_square_strict
.else
    mov ecx, \n
.Lzr_loop\@:
    call .Lzr_square_strict
    dec ecx
    jne .Lzr_loop\@
.endif
.endm
.macro zr_save_slot slot
.if \slot
    zr_store rsi, (320*(\slot-1))
.endif
.endm
.macro zr_multiply_slot slot
.if \slot
    lea r8, [rsi + 320*(\slot-1)]
.else
    lea r8, [rbx + 960]
.endif
    call .Lzr_chain_product
.endm
.Lzr_chain_product:
    call .Lzr_mul_memory
    // Tighten the three limbs doubled in the square kernel.
    vpsrlq zmm20, zmm2, 51
    vpandq zmm2, zmm2, zmm29
    vpaddq zmm3, zmm3, zmm20
    vpsrlq zmm21, zmm4, 51
    vpandq zmm4, zmm4, zmm29
    vpmadd52luq zmm0, zmm21, zmm28
    vpsrlq zmm21, zmm0, 51
    vpandq zmm0, zmm0, zmm29
    vpaddq zmm1, zmm1, zmm21
    ret
// Slot 0 is uv in the point. Slots 1 and 2 occupy the two stack fields.
.Lzr_power_single:
    zr_load rbx, 960
    fe51_pow22523 zr_save_slot, zr_multiply_slot, zr_squares
    zr_store rsi, 0
    ret

.Lzr_mul_sqrt_m1:
.irp i,5,6,7,8,9
    vpbroadcastq zmm\i, qword ptr [rip + .Ltor_sqrt_m1 + 8*(\i-5)]
.endr
    jmp .Lzr_product
.Lzr_mul_memory:
.irp i,5,6,7,8,9
    vmovdqa64 zmm\i, [r8 + 64*(\i-5)]
.endr
.Lzr_product:
    call .Ltor_columns
.Lzr_reduce:
    // Carry columns independently. With the 1024*p bias the outgoing
    // carries are below 1700. Even the folded low limb fits in 52 bits.
.macro zr_carry i, next
    vpsrlq zmm\next, zmm\i, 51
    vpandq zmm\i, zmm\i, zmm29
.endm
.irp i,0,1,2,3,4
    zr_carry \i, %(10+\i)
.endr
    vpmadd52luq zmm0, zmm14, zmm28
.macro zr_add_carry i, previous
    vpaddq zmm\i, zmm\i, zmm\previous
.endm
.irp i,1,2,3,4
    zr_add_carry \i, %(9+\i)
.endr
    ret

.balign 64
.Lzr_even: .quad 0,2,4,6,8,10,12,14
.Lzr_odd: .quad 1,3,5,7,9,11,13,15
.Lzr_one: .quad 1
.Lzr_p0: .quad (1 << 51) - 19
.Lzr_p0_plus_one: .quad (1 << 51) - 18
.Lzr_p0_minus_one: .quad (1 << 51) - 20
.Lzr_twice_p0: .quad 2*((1 << 51) - 19)
.size ed25519_simd_zip215_decode_r, .-ed25519_simd_zip215_decode_r
.purgem zr_load
.purgem zr_store
.purgem zr_constants
.purgem zr_scale_limb
.purgem zr_scaled_uv
.purgem zr_high_ones
.purgem zr_squares
.purgem zr_save_slot
.purgem zr_multiply_slot
.purgem fe51_square
.purgem fe51_pow22523
.purgem zr_carry
.purgem zr_add_carry
.noaltmacro
.popsection
