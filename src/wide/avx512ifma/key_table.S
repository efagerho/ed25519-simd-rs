// Build signed radix-16 public-key tables from eight decoded affine points.
// SysV RDI is an exclusive 64-byte-aligned WidePoint used as the running multiple.
// Its limbs are < 2^52 and Z=1. RSI is disjoint writable storage for RDX
// consecutive 2720-byte, 8-byte-aligned tables. RDX=8 selects all lanes, RDX=1 only lane 0.
// Entry 8+j represents [j]P as (Y-X,Y+X,2dT,2Z), each five u64s < 2^52.
// All bytes are initialized even for lanes rejected by the decoder.
// Preserve SysV callee-saved registers. Stack use including the nested
// cached addition is at most 2424 bytes below the entry stack pointer.
.pushsection .text.ed25519_simd_build_key_tables,"ax",@progbits
.p2align 4
.globl ed25519_simd_build_key_tables
.hidden ed25519_simd_build_key_tables
.type ed25519_simd_build_key_tables,@function

// Save the positive affine operand in add_cached.S field order.
.macro kt_stage offset, a,b,c,d,e
    vmovdqa64 [rsp + \offset], zmm\a
    vmovdqa64 [rsp + \offset + 64], zmm\b
    vmovdqa64 [rsp + \offset + 128], zmm\c
    vmovdqa64 [rsp + \offset + 192], zmm\d
    vmovdqa64 [rsp + \offset + 256], zmm\e
.endm

// Join pairs of limbs into groups of four, then join the groups into
// one eight-word row for each of two keys.
.macro kt_join a,b,c,d, select, low, high
    vshufi64x2 zmm28, zmm\a, zmm\b, \select
    vshufi64x2 zmm29, zmm\c, zmm\d, \select
    vshufi64x2 zmm\low, zmm28, zmm29, 0x88
    vshufi64x2 zmm\high, zmm28, zmm29, 0xdd
.endm

// Transpose eight successive limb vectors in place. On return a..h hold
// the corresponding eight words for keys 0..7. first_only produces just a.
.macro kt_eight a,b,c,d,e,f,g,h, first_only=0
    vpunpcklqdq zmm10, zmm\a, zmm\b
    vpunpcklqdq zmm12, zmm\c, zmm\d
    vpunpcklqdq zmm14, zmm\e, zmm\f
    vpunpcklqdq zmm26, zmm\g, zmm\h
.if \first_only
    vshufi64x2 zmm28, zmm10, zmm12, 0x88
    vshufi64x2 zmm29, zmm14, zmm26, 0x88
    vshufi64x2 zmm\a, zmm28, zmm29, 0x88
.else
    vpunpckhqdq zmm11, zmm\a, zmm\b
    vpunpckhqdq zmm13, zmm\c, zmm\d
    vpunpckhqdq zmm15, zmm\e, zmm\f
    vpunpckhqdq zmm27, zmm\g, zmm\h
    kt_join 10,12,14,26, 0x88, \a, \e
    kt_join 10,12,14,26, 0xdd, \c, \g
    kt_join 11,13,15,27, 0x88, \b, \f
    kt_join 11,13,15,27, 0xdd, \d, \h
.endif
.endm

// The last four words are limbs 1..4 of 2Z, identical for both signs.
.macro kt_four unpack
    \unpack zmm10, zmm1, zmm2
    \unpack zmm11, zmm3, zmm4
    vshufi64x2 zmm12, zmm10, zmm11, 0x44
    vshufi64x2 zmm13, zmm10, zmm11, 0xee
    vshufi64x2 zmm10, zmm12, zmm13, 0x88
    vshufi64x2 zmm11, zmm12, zmm13, 0xdd
.endm

// Store the positive row, then permute its first 16 qwords to swap Y-X
// and Y+X. Bits 2..6 of the second vector hold 2dT. Each carried limb is
// below 2^51 + 19*1700, so digitwise 2p - 2dT stays in [0, 2^52).
.macro kt_row lane, a, b, tail, half
    vmovdqu64 [r13 + 2720*\lane], zmm\a
    vmovdqu64 [r13 + 2720*\lane + 64], zmm\b
    vmovdqa64 zmm12, zmm\a
    vpermt2q zmm12, zmm28, zmm\b
    vpermt2q zmm\a, zmm29, zmm\b
    vpsubq zmm\a{k1}, zmm30, zmm\a
    vmovdqu64 [r14 + 2720*\lane], zmm12
    vmovdqu64 [r14 + 2720*\lane + 64], zmm\a
    vextracti64x4 [r13 + 2720*\lane + 128], zmm\tail, \half
    vextracti64x4 [r14 + 2720*\lane + 128], zmm\tail, \half
.endm

.macro kt_keep_field a,b,c,d,e
    vmovdqa64 zmm\a, zmm0
    vmovdqa64 zmm\b, zmm1
    vmovdqa64 zmm\c, zmm2
    vmovdqa64 zmm\d, zmm3
    vmovdqa64 zmm\e, zmm4
.endm

ed25519_simd_build_key_tables:
    push rbp
    mov rbp, rsp
    push rbx
    push r12
    push r13
    push r14
    push r15
    and rsp, -64
    sub rsp, 960                    // staged affine P
    mov r12, rdi
    lea r13, [rsi + 8*160]          // positive and negative cursors start at [0]P
    mov r14, r13
    mov ebx, edx
    mov rax, r13
    mov ecx, edx
    vpxorq zmm0, zmm0, zmm0
.Lkt_identity_lane:
    vmovdqu64 [rax], zmm0
    vmovdqu64 [rax + 64], zmm0
    vmovdqu [rax + 128], ymm0
    mov qword ptr [rax], 1
    mov qword ptr [rax + 40], 1
    mov qword ptr [rax + 120], 2
    add rax, 2720
    dec ecx
    jne .Lkt_identity_lane

    mov r15d, 1
.Lkt_multiple:
    add r13, 160
    sub r14, 160
    fe51_constants
    fe51_load r12, 960
.irp i,5,6,7,8,9
    vpbroadcastq zmm\i, qword ptr [rip + .Lkt_two_d + 8*(\i-5)]
.endr
    call .Lzr_product               // carried 2dT in ZMM0..4
    kt_keep_field 5,6,7,8,9

    fe51_load r12, 320
.irp i,0,1,2,3,4
.if \i == 0
    vpaddq zmm0, zmm0, zmm30
.else
    vpaddq zmm\i, zmm\i, zmm31
.endif
    vpsubq zmm\i, zmm\i, [r12 + 64*\i]
.endr
    call .Lfe51_carry               // Y + 1024*p - X
    kt_keep_field 16,17,18,19,20

    fe51_load r12, 320
.irp i,0,1,2,3,4
    vpaddq zmm\i, zmm\i, [r12 + 64*\i]
.endr
    call .Lfe51_carry
    kt_keep_field 21,22,23,24,25

    fe51_load r12, 640
.irp i,0,1,2,3,4
    vpaddq zmm\i, zmm\i, zmm\i
.endr
    call .Lfe51_carry
    cmp r15d, 1
    jne .Lkt_pack
    kt_stage 0, 16,17,18,19,20
    kt_stage 320, 21,22,23,24,25
    kt_stage 640, 5,6,7,8,9
.Lkt_pack:
    // Entry word order is Y-X (ZMM16..20), Y+X (21..25), 2dT (5..9),
    // then 2Z (0..4). Pack the two full cache lines followed by four words.
    cmp ebx, 1
    je .Lkt_single
    kt_eight 16,17,18,19,20,21,22,23
    kt_eight 24,25,5,6,7,8,9,0
    jmp .Lkt_packed
.Lkt_single:
    kt_eight 16,17,18,19,20,21,22,23, 1
    kt_eight 24,25,5,6,7,8,9,0, 1
.Lkt_packed:
    vmovdqa64 zmm28, [rip + .Lkt_neg_words0]
    vmovdqa64 zmm29, [rip + .Lkt_neg_words8]
    vmovdqa64 zmm30, [rip + .Lkt_neg_bias]
    mov eax, 0x7c
    kmovw k1, eax
    kt_four vpunpcklqdq
    kt_row 0, 16, 24, 10, 0
    cmp ebx, 1
    je .Lkt_row_done
    kt_row 4, 20, 7, 10, 1
    kt_row 2, 18, 5, 11, 0
    kt_row 6, 22, 9, 11, 1
    kt_four vpunpckhqdq
    kt_row 1, 17, 25, 10, 0
    kt_row 5, 21, 8, 10, 1
    kt_row 3, 19, 6, 11, 0
    kt_row 7, 23, 0, 11, 1
.Lkt_row_done:

    cmp r15d, 8
    je .Lkt_done
    mov rdi, r12
    mov rsi, rsp
    mov edx, 1                      // preserve T for the next cached entry
    mov ecx, 1                      // P is affine
    call ed25519_simd_add_cached_ifma
    inc r15d
    jmp .Lkt_multiple
.Lkt_done:
    lea rsp, [rbp - 40]
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    pop rbp
    vzeroupper
    ret

.balign 64
// Swap source words 0..4 with 5..9 and keep 10..15 in place. The last
// four words of 2Z are copied separately from the same register for both signs.
.Lkt_neg_words0:  .quad 5,6,7,8,9,0,1,2
.Lkt_neg_words8: .quad 3,4,10,11,12,13,14,15
.Lkt_neg_bias:
    .quad 0, 0, (1<<52)-38, (1<<52)-2, (1<<52)-2, (1<<52)-2, (1<<52)-2, 0
// 2*d mod p, little-endian radix-2^51 limbs.
.Lkt_two_d:
    .quad 1859910466990425, 932731440258426, 1072319116312658, 1815898335770999, 633789495995903
.size ed25519_simd_build_key_tables, .-ed25519_simd_build_key_tables
.purgem kt_stage
.purgem kt_keep_field
.purgem kt_join
.purgem kt_eight
.purgem kt_four
.purgem kt_row
.popsection
