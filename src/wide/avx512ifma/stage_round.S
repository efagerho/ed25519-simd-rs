// SysV AMD64, AVX-512F. Select and transpose one public radix-256 round.
// RDI: exclusive, 64-byte-aligned StagedLadderStep (3520 bytes).
// RSI: eight pointers to the first of 17 consecutive 160-byte key entries,
//      ordered [-8]P .. [8]P. Pointers may repeat.
// RDX: first of 273 consecutive 120-byte affine entries, [-136]B .. [136]B.
// RCX, R8: s and k respectively, eight lane-major rows of 64 signed bytes.
// R9: pair 0..31. Even is digit 2*pair and odd is its successor.
// Each entry is (Y-X, Y+X, 2dT, projective-only 2Z), five u64s per field.
// Output is odd key, folded base, even key. Within each operand, output
// qword 8*i+lane copies qword i of that lane's selected entry. All limb
// bits are preserved. Tables and digits are read-only and disjoint from
// the output. Table addresses depend on public digits. The leaf uses only
// caller-saved registers and writes only to the output. Only RET touches RSP.

// Combine four words from two lanes into the low and high halves of a ZMM.
// Pair lanes 0/2, 1/3, 4/6 and 5/7 so the final shuffle puts lanes in order.
.macro stage_half reg, upper, address:vararg
    .if \upper
        vinserti64x4 zmm\reg, zmm\reg, ymmword ptr [\address], 1
    .else
        vmovdqu ymm\reg, [\address]
    .endif
.endm

// Keep the eight-word tile in zmm16..23, one row per lane. Each group of
// four-word tiles occupies four more ZMM registers, paired as above.
.macro stage_lane kind, lane, full, upper, a, b, c
    .ifc \kind,base
        // 136 + s_even + 16*s_odd is the byte formed from the two low
        // nibbles, each biased by 8. Only these eight bits index the table.
        movzx eax, word ptr [rcx + 64*\lane]
        mov r11d, eax
        shr r11d, 4
        and eax, 15
        and r11d, 240
        or eax, r11d
        xor eax, 0x88
        imul eax, eax, 120
        vmovdqu64 \full, [rdx + rax]
        stage_half \a, \upper, rdx + rax + 64
        stage_half \b, \upper, rdx + rax + 88
    .else
        // 8-k = 1 + ((k & 15) XOR 7). Fold entry 1 into the load
        // displacements; its offset from the start of the table is 160.
        movzx eax, byte ptr [r8 + 64*\lane + \kind]
        and eax, 15
        xor eax, 7
        imul eax, eax, 160
        add rax, [rsi + 8*\lane]
        stage_half \a, \upper, rax + 160
        stage_half \b, \upper, rax + 160 + 32
        vmovdqu64 \full, [rax + 160 + 64]
        stage_half \c, \upper, rax + 160 + 128
    .endif
.endm

// Emit four columns from paired half rows. Unpacking forms pairs of lanes.
// 0x88 selects 128-bit blocks 0 and 2 from each source, 0xdd selects 1 and 3.
.macro stage_four a, b, c, d, dest, skip_first=0
    vpunpcklqdq zmm24, \a, \b
    vpunpcklqdq zmm25, \c, \d
    .if !\skip_first
        vshufi64x2 zmm26, zmm24, zmm25, 0x88
        vmovdqa64 [rdi + \dest], zmm26
    .endif
    vshufi64x2 zmm27, zmm24, zmm25, 0xdd
    vmovdqa64 [rdi + \dest + 128], zmm27
    vpunpckhqdq zmm24, \a, \b
    vpunpckhqdq zmm25, \c, \d
    vshufi64x2 zmm26, zmm24, zmm25, 0x88
    vshufi64x2 zmm27, zmm24, zmm25, 0xdd
    vmovdqa64 [rdi + \dest + 64], zmm26
    vmovdqa64 [rdi + \dest + 192], zmm27
.endm

.macro stage_blocks select, dest
    vshufi64x2 zmm28, zmm24, zmm25, \select
    vshufi64x2 zmm29, zmm26, zmm27, \select
    vshufi64x2 zmm30, zmm28, zmm29, 0x88
    vshufi64x2 zmm31, zmm28, zmm29, 0xdd
    vmovdqa64 [rdi + \dest], zmm30
    vmovdqa64 [rdi + \dest + 256], zmm31
.endm

// Transpose eight full rows. The unpack selects even or odd words. The
// first shuffle groups four lanes and the second joins all eight lanes.
.macro stage_parity unpack, dest
    \unpack zmm24, zmm16, zmm17
    \unpack zmm25, zmm18, zmm19
    \unpack zmm26, zmm20, zmm21
    \unpack zmm27, zmm22, zmm23
    stage_blocks 0x88, \dest
    stage_blocks 0xdd, \dest + 128
.endm

.macro stage_operand kind, dest
    stage_lane \kind, 0, zmm16, 0, 0, 4, 8
    stage_lane \kind, 1, zmm17, 0, 1, 5, 9
    stage_lane \kind, 2, zmm18, 1, 0, 4, 8
    stage_lane \kind, 3, zmm19, 1, 1, 5, 9
    stage_lane \kind, 4, zmm20, 0, 2, 6, 10
    stage_lane \kind, 5, zmm21, 0, 3, 7, 11
    stage_lane \kind, 6, zmm22, 1, 2, 6, 10
    stage_lane \kind, 7, zmm23, 1, 3, 7, 11
    .ifc \kind,base
        stage_parity vpunpcklqdq, \dest
        stage_parity vpunpckhqdq, \dest + 64
        stage_four zmm0, zmm1, zmm2, zmm3, \dest + 512
        // Read words 11..14 to end exactly at the entry boundary. Word 11
        // was emitted by the preceding tile, so skip its store.
        stage_four zmm4, zmm5, zmm6, zmm7, \dest + 704, 1
    .else
        stage_four zmm0, zmm1, zmm2, zmm3, \dest
        stage_four zmm4, zmm5, zmm6, zmm7, \dest + 256
        stage_parity vpunpcklqdq, \dest + 512
        stage_parity vpunpckhqdq, \dest + 576
        stage_four zmm8, zmm9, zmm10, zmm11, \dest + 1024
    .endif
.endm

.text
.p2align 4
.globl ed25519_simd_stage_round
.hidden ed25519_simd_stage_round
.type ed25519_simd_stage_round,@function
ed25519_simd_stage_round:
    lea rcx, [rcx + 2*r9]
    lea r8, [r8 + 2*r9]
    stage_operand 1, 0
    stage_operand base, 1280
    stage_operand 0, 2240
    vzeroupper
    ret
.size ed25519_simd_stage_round, .-ed25519_simd_stage_round
.purgem stage_half
.purgem stage_lane
.purgem stage_four
.purgem stage_blocks
.purgem stage_parity
.purgem stage_operand
