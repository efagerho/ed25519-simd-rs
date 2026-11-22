// SysV AMD64. RSI points to eight 64-byte rows of digest words, RDI to a
// disjoint 512-byte output. Neither buffer requires alignment. On return,
// byte 64*lane + j is signed digit j of that lane's canonical residue mod L.
// The only stack writes below entry RSP are the saved RDI and the nested
// return address. Control flow and memory addresses are independent of H.
.text
.p2align 4
.globl ed25519_simd_digest_to_radix16
.hidden ed25519_simd_digest_to_radix16
.type ed25519_simd_digest_to_radix16,@function

// Include the carry from lower limbs before extracting the next word.
.macro r16_carry lo, hi
    vpsrlq zmm6, \lo, 52
    vpaddq \hi, \hi, zmm6
.endm

// Expand one word per scalar to sixteen signed digit bytes. Unpacking acts
// within 128-bit blocks, giving lanes 0,2,4,6 in even and 1,3,5,7 in odd.
.macro r16_expand word, even, odd
    vpsrlq zmm7, \word, 4
    vpandq zmm7, zmm7, zmm5
    vpandq \word, \word, zmm5
    vpsubb zmm7, zmm7, zmm6
    vpsubb \word, \word, zmm6
    vpunpcklbw \even, \word, zmm7
    vpunpckhbw \odd, \word, zmm7
.endm

// Each input holds four 16-digit blocks from word a, b, c, or d. Select
// blocks 0/1 (0x44) or 2/3 (0xee). For example, [a0,a1,b0,b1] and
// [c0,c1,d0,d1] give [a0,b0,c0,d0] with 0x88 and [a1,b1,c1,d1] with 0xdd.
.macro r16_store_pair a, b, c, d, blocks, lane
    vshufi64x2 zmm0, \a, \b, \blocks
    vshufi64x2 zmm1, \c, \d, \blocks
    vshufi64x2 zmm2, zmm0, zmm1, 0x88
    vshufi64x2 zmm3, zmm0, zmm1, 0xdd
    vmovdqu64 [rdi + 64*\lane], zmm2
    vmovdqu64 [rdi + 64*(\lane+2)], zmm3
.endm

// ZMM0..3 hold the four little-endian words of each biased scalar.
.macro r16_write_digits
    mov eax, 15
    vpbroadcastb zmm5, eax
    mov eax, 8
    vpbroadcastb zmm6, eax
    r16_expand zmm0, zmm8, zmm9
    r16_expand zmm1, zmm10, zmm11
    r16_expand zmm2, zmm12, zmm13
    r16_expand zmm3, zmm14, zmm15

    r16_store_pair zmm8, zmm10, zmm12, zmm14, 0x44, 0
    r16_store_pair zmm9, zmm11, zmm13, zmm15, 0x44, 1
    r16_store_pair zmm8, zmm10, zmm12, zmm14, 0xee, 4
    r16_store_pair zmm9, zmm11, zmm13, zmm15, 0xee, 5
.endm

ed25519_simd_digest_to_radix16:
    // The 320-byte reducer destination fits in the digit output. Saving
    // its address also aligns RSP to 16 bytes for the SysV call.
    push rdi
    call ed25519_simd_scalar_reduce_ifma
    pop rdi

    // Let b[i] = limb[i] + thirteen nibbles of 8. Adding the same bias
    // across the low 256 bits cannot overflow because the scalar is below L.
    mov rax, 0x8888888888888
    vpbroadcastq zmm5, rax
.irp i,0,1,2,3,4
    vpaddq zmm\i, zmm5, [rdi + 64*\i]
.endr
    // Word i starts 12*i bits into limb i. Let t[i] be b[i] plus its
    // incoming carry. The word is the low 64 bits of
    //   (t[i] >> (12*i)) + (b[i+1] << (52-12*i)).
    // The addition includes the possible 53rd bit of t[i]. Form the high
    // fragments from b[i+1] before propagating carries to avoid counting it twice.
    vpsllq zmm8, zmm1, 52
    vpsllq zmm9, zmm2, 40
    vpsllq zmm10, zmm3, 28
    vpsllq zmm11, zmm4, 16

    r16_carry zmm0, zmm1
    vpaddq zmm0, zmm0, zmm8
    r16_carry zmm1, zmm2
    vpsrlq zmm1, zmm1, 12
    vpaddq zmm1, zmm1, zmm9
    r16_carry zmm2, zmm3
    vpsrlq zmm2, zmm2, 24
    vpaddq zmm2, zmm2, zmm10
    vpsrlq zmm3, zmm3, 36
    vpaddq zmm3, zmm3, zmm11

    r16_write_digits
    vzeroupper
    ret
.size ed25519_simd_digest_to_radix16, .-ed25519_simd_digest_to_radix16

// SysV AMD64. RSI points to eight read-only pointers to little-endian S[32].
// Input pointers may repeat. RDI points to a disjoint, unaligned 512-byte
// output. Bit i of EAX is set iff S[i] < L. Row i contains 64 signed digits
// of S[i] in that case and 64 zero bytes otherwise. No stack scratch or calls.
.p2align 4
.globl ed25519_simd_prepare_signature_scalars
.hidden ed25519_simd_prepare_signature_scalars
.type ed25519_simd_prepare_signature_scalars,@function
ed25519_simd_prepare_signature_scalars:
    // Pair rows 0/2, 1/3, 4/6, 5/7. The unpack pairs adjacent lanes,
    // and the shuffle joins the two groups of four lanes in word order.
.macro s_load_pair reg, low, high
    mov rax, [rsi + 8*\low]
    mov rcx, [rsi + 8*\high]
    vmovdqu ymm\reg, [rax]
    vinserti64x4 zmm\reg, zmm\reg, [rcx], 1
.endm
    s_load_pair 0, 0, 2
    s_load_pair 1, 1, 3
    s_load_pair 2, 4, 6
    s_load_pair 3, 5, 7
    vpunpcklqdq zmm4, zmm0, zmm1
    vpunpcklqdq zmm5, zmm2, zmm3
    vpunpckhqdq zmm6, zmm0, zmm1
    vpunpckhqdq zmm7, zmm2, zmm3
    vshufi64x2 zmm8, zmm4, zmm5, 0x88
    vshufi64x2 zmm9, zmm6, zmm7, 0x88
    vshufi64x2 zmm10, zmm4, zmm5, 0xdd
    vshufi64x2 zmm11, zmm6, zmm7, 0xdd

    // Compare unsigned 64-bit words from least to most significant.
    // A higher word wins unless equal. Word 2 of L is zero.
    vpcmpuq k1, zmm8, qword ptr [rip + .Ls_order]{1to8}, 1
    vpcmpeqq k1{k1}, zmm9, qword ptr [rip + .Ls_order + 8]{1to8}
    vpcmpuq k2, zmm9, qword ptr [rip + .Ls_order + 8]{1to8}, 1
    korw k1, k1, k2
    vpxorq zmm4, zmm4, zmm4
    vpcmpeqq k1{k1}, zmm10, zmm4
    vpcmpeqq k1{k1}, zmm11, qword ptr [rip + .Ls_order + 24]{1to8}
    vpcmpuq k2, zmm11, qword ptr [rip + .Ls_order + 24]{1to8}, 1
    korw k1, k1, k2

    // Bias all 64 nibbles by 8. A word addition including carry-in
    // carries out exactly when its unsigned result is below its input.
    mov rax, 0x8888888888888888
    vpbroadcastq zmm4, rax
    mov eax, 1
    vpbroadcastq zmm5, rax
    vpaddq zmm0, zmm8, zmm4
    vpaddq zmm1, zmm9, zmm4
    vpaddq zmm2, zmm10, zmm4
    vpaddq zmm3, zmm11, zmm4
    vpcmpuq k2, zmm0, zmm8, 1
    vpaddq zmm1{k2}, zmm1, zmm5
    vpcmpuq k2, zmm1, zmm9, 1
    vpaddq zmm2{k2}, zmm2, zmm5
    vpcmpuq k2, zmm2, zmm10, 1
    vpaddq zmm3{k2}, zmm3, zmm5

    // Select the bias itself for rejected lanes, giving signed digit zero
    // in every position when r16_write_digits subtracts 8.
.irp i,0,1,2,3
    vpblendmq zmm\i{k1}, zmm4, zmm\i
.endr
    r16_write_digits
    kmovw eax, k1
    vzeroupper
    ret
.size ed25519_simd_prepare_signature_scalars, .-ed25519_simd_prepare_signature_scalars
.purgem s_load_pair
.purgem r16_write_digits
.purgem r16_carry
.purgem r16_expand
.purgem r16_store_pair

.pushsection .rodata
.p2align 3
.Ls_order:
    .quad 0x5812631a5cf5d3ed, 0x14def9dea2f79cd6, 0, 0x1000000000000000
.popsection
