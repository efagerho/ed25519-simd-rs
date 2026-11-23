// Eight SHA-512 challenges, lane j hashing R[j] || A[j] || message[j].
// SysV AMD64: RDI = 512 writable digest bytes, RSI/RDX = eight consecutive
// 32-byte R/key encodings, RCX = eight message pointers, R8 = eight lengths.
// Inputs may alias each other. Each message has exactly its stated readable
// length (at most isize::MAX); zero-length messages need no readable bytes.
// Output is disjoint from inputs. No external buffer needs vector alignment.
// Qword [8*word+lane] in the output contains the eight digest bytes in their
// original order, as expected by ed25519_simd_digest_to_radix16.

.pushsection .text.ed25519_simd_sha512_challenge,"ax",@progbits
.altmacro

// For m message bytes, the last zero-based block is floor((m+64+16)/128).
// The SHA-512 trailer is the 128-bit big-endian bit count of R || A || M.
.macro sha512_lengths lengths
    vmovdqu64 zmm24, [\lengths]
    vpaddq zmm25, zmm24, qword ptr [rip + .Lsha_prefix_bytes]{1to8}
    vpaddq zmm26, zmm24, qword ptr [rip + .Lsha_last_bias]{1to8}
    vpsrlq zmm24, zmm25, 61
    vpsllq zmm25, zmm25, 3
    vpsrlq zmm26, zmm26, 7
.endm

// Eight 64-byte rows in ZMM8..15 -> eight big-endian word columns.
// Unpack pairs of lanes, join quartets, then join the two halves.
.macro sha512_unpack a,b,lo,hi
    vpunpcklqdq zmm\lo, zmm\a, zmm\b
    vpunpckhqdq zmm\hi, zmm\a, zmm\b
.endm
.macro sha512_join a,b,lo,hi
    vshufi64x2 zmm\lo, zmm\a, zmm\b, 0x88
    vshufi64x2 zmm\hi, zmm\a, zmm\b, 0xdd
.endm
.macro sha512_swap_word dst,src
    vpshufb zmm\dst, zmm\src, zmm8
.endm
.macro sha512_transpose first
    sha512_unpack 8,9,24,25
    sha512_unpack 10,11,26,27
    sha512_unpack 12,13,28,29
    sha512_unpack 14,15,30,31
    sha512_join 24,26,8,10
    sha512_join 28,30,9,11
    sha512_join 25,27,12,14
    sha512_join 29,31,13,15
    sha512_join 8,9,24,28
    sha512_join 10,11,26,30
    sha512_join 12,13,25,29
    sha512_join 14,15,27,31
    // Write W8 last when transposing the upper half: it holds the byte mask.
    vmovdqa64 zmm8, [rip + .Lsha_swap]
.irp i,7,6,5,4,3,2,1,0
    sha512_swap_word %(\first+\i), %(24+\i)
.endr
.endm

// Extend the 16-word schedule ring in place.
// W[t] = W[t-16] + s0(W[t-15]) + W[t-7] + s1(W[t-2]).
.macro sha512_expand w,w15,w7,w2
    vprorq zmm24, zmm\w15, 1
    vprorq zmm25, zmm\w15, 8
    vpsrlq zmm26, zmm\w15, 7
    vprorq zmm27, zmm\w2, 19
    vprorq zmm28, zmm\w2, 61
    vpsrlq zmm29, zmm\w2, 6
    vpternlogq zmm24, zmm25, zmm26, 0x96
    vpternlogq zmm27, zmm28, zmm29, 0x96
    vpaddq zmm24, zmm24, zmm\w
    vpaddq zmm27, zmm27, zmm\w7
    vpaddq zmm\w, zmm24, zmm27
.endm

// Start both h+K+W and d+(h+K+W) early. Adding Ch and then Sigma1 to each
// gives T1 and d+T1 on independent paths. Add Maj to T1 while the three
// rotations and XOR for Sigma0(a) finish, then add Sigma0 last.
// The next round uses the old d and h registers for its new e and a.
.macro sha512_round w,a,b,c,d,e,f,g,h,expand
    vpaddq zmm24, zmm\w, qword ptr [r10 + 8*\w]{1to8}
    vprorq zmm25, zmm\e, 14
    vprorq zmm26, zmm\e, 18
    vprorq zmm27, zmm\e, 41
    vmovdqa64 zmm28, zmm\e
    vpternlogq zmm28, zmm\f, zmm\g, 0xca
    vprorq zmm29, zmm\a, 28
    vprorq zmm30, zmm\a, 34
    vprorq zmm31, zmm\a, 39
    vpternlogq zmm25, zmm26, zmm27, 0x96
    vpaddq zmm\h, zmm\h, zmm24
    vpaddq zmm\d, zmm\d, zmm\h
    vmovdqa64 zmm24, zmm\a
    vpternlogq zmm24, zmm\b, zmm\c, 0xe8
    vpternlogq zmm29, zmm30, zmm31, 0x96
    vpaddq zmm\d, zmm\d, zmm28
    vpaddq zmm28, zmm28, zmm\h
    vpaddq zmm\d, zmm\d, zmm25
    vpaddq zmm\h, zmm28, zmm25
    vpaddq zmm\h, zmm\h, zmm24
    vpaddq zmm\h, zmm\h, zmm29
    // W[t] has been consumed. Replace it with W[t+16] for the next group.
.if \expand
    sha512_expand \w, %((\w+1)&15), %((\w+9)&15), %((\w+14)&15)
.endif
.endm
.macro sha512_rounds expand
.irp base,0,8
    sha512_round %(\base+0), 16,17,18,19,20,21,22,23, \expand
    sha512_round %(\base+1), 23,16,17,18,19,20,21,22, \expand
    sha512_round %(\base+2), 22,23,16,17,18,19,20,21, \expand
    sha512_round %(\base+3), 21,22,23,16,17,18,19,20, \expand
    sha512_round %(\base+4), 20,21,22,23,16,17,18,19, \expand
    sha512_round %(\base+5), 19,20,21,22,23,16,17,18, \expand
    sha512_round %(\base+6), 18,19,20,21,22,23,16,17, \expand
    sha512_round %(\base+7), 17,18,19,20,21,22,23,16, \expand
.endr
.endm

.macro sha512_prefix lane,reg
    vmovdqu ymm\reg, [rsi + 32*\lane]
    vinserti64x4 zmm\reg, zmm\reg, ymmword ptr [rdx + 32*\lane], 1
.endm
.p2align 4
.globl ed25519_simd_sha512_challenge
.hidden ed25519_simd_sha512_challenge
.type ed25519_simd_sha512_challenge,@function
ed25519_simd_sha512_challenge:
    push rbp
    mov rbp, rsp
    and rsp, -64
    sub rsp, 704                    // eight state words, high/low bit length, last block
    mov r9, rcx                     // message pointers
    mov r11, r8                     // message lengths
    sha512_lengths r11
    vmovdqa64 [rsp + 512], zmm24
    vmovdqa64 [rsp + 576], zmm25
    vmovdqa64 [rsp + 640], zmm26
.irp reg,16,17,18,19,20,21,22,23
    vpbroadcastq zmm\reg, qword ptr [rip + .Lsha_iv + 8*(\reg-16)]
.endr
.irp i,0,1,2,3,4,5,6,7
    sha512_prefix \i, %(8+\i)
.endr
    xor esi, esi                    // current block
    xor r8d, r8d                    // offset of next 64 message bytes
.Lsha_block:
    sha512_transpose 0
    call .Lsha_message_rows
    sha512_transpose 8
    vpbroadcastq zmm24, rsi
    vpcmpeqq k4, zmm24, [rsp + 640] // lanes finishing this block
    vpcmpuq k5, zmm24, [rsp + 640], 1 // lanes with another block
    vmovdqa64 zmm14{k4}, [rsp + 512]
    vmovdqa64 zmm15{k4}, [rsp + 576]

.irp reg,16,17,18,19,20,21,22,23
    vmovdqa64 [rsp + 64*(\reg-16)], zmm\reg
.endr
    lea r10, [rip + .Lsha_k]
    lea rdx, [rip + .Lsha_k_end - 128]
.Lsha_expanded:
    sha512_rounds 1
    add r10, 128
    cmp r10, rdx
    jne .Lsha_expanded
    sha512_rounds 0
.irp reg,16,17,18,19,20,21,22,23
    vpaddq zmm\reg, zmm\reg, [rsp + 64*(\reg-16)]
.endr

    // Publish each lane once. Later blocks can freely overwrite its registers.
    kortestw k4, k4
    jz .Lsha_next
    vmovdqa64 zmm25, [rip + .Lsha_swap]
.irp reg,16,17,18,19,20,21,22,23
    vpshufb zmm24, zmm\reg, zmm25
    vmovdqu64 [rdi + 64*(\reg-16)]{k4}, zmm24
.endr
.Lsha_next:
    kortestw k5, k5
    jz .Lsha_return
    inc rsi
    call .Lsha_message_rows
    jmp .Lsha_block
.Lsha_return:
    mov rsp, rbp
    pop rbp
    vzeroupper
    ret

// Load the next half-block in each lane and advance the message offset.
// The common full-row path has no per-lane length branches.
.macro sha512_full_row lane,reg
    mov r10, [r9 + 8*\lane]
    vmovdqu64 zmm\reg, [r10 + r8]
.endm
.macro sha512_tail_row lane,reg
    mov rcx, [r11 + 8*\lane]
    sub rcx, r8
    jb .Lsha_empty\@
    mov r10, [r9 + 8*\lane]
    cmp rcx, 64
    jae .Lsha_full\@
    // Read exactly count bytes and insert 0x80 in byte count (0..63).
    mov eax, 1
    shl rax, cl
    kmovq k1, rax
    dec rax
    kmovq k2, rax
    vmovdqu8 zmm\reg{k2}{z}, [r10 + r8]
    vmovdqu8 zmm\reg{k1}, zmm24
    jmp .Lsha_loaded\@
.Lsha_full\@:
    vmovdqu64 zmm\reg, [r10 + r8]
    jmp .Lsha_loaded\@
.Lsha_empty\@:
    vpxord zmm\reg, zmm\reg, zmm\reg
.Lsha_loaded\@:
.endm
.Lsha_message_rows:
    lea rax, [r8 + 64]
    vpbroadcastq zmm24, rax
    vpcmpuq k1, zmm24, [r11], 6   // any length less than offset + 64?
    kortestw k1, k1
    jnz .Lsha_tails
.irp i,0,1,2,3,4,5,6,7
    sha512_full_row \i, %(8+\i)
.endr
    add r8, 64
    ret
.Lsha_tails:
    mov eax, 0x80
    vpbroadcastb zmm24, eax
.irp i,0,1,2,3,4,5,6,7
    sha512_tail_row \i, %(8+\i)
.endr
    add r8, 64
    ret
.size ed25519_simd_sha512_challenge, .-ed25519_simd_sha512_challenge

// Exercise the production length calculations with sizes too large to allocate.
.ifdef .Lsha512_test
.globl ed25519_simd_test_sha512_lengths
.hidden ed25519_simd_test_sha512_lengths
.type ed25519_simd_test_sha512_lengths,@function
ed25519_simd_test_sha512_lengths:
    sha512_lengths rsi
    vmovdqu64 [rdi], zmm24
    vmovdqu64 [rdi+64], zmm25
    vmovdqu64 [rdi+128], zmm26
    vzeroupper
    ret
.size ed25519_simd_test_sha512_lengths, .-ed25519_simd_test_sha512_lengths
.endif
.noaltmacro
.purgem sha512_lengths
.purgem sha512_unpack
.purgem sha512_join
.purgem sha512_transpose
.purgem sha512_swap_word
.purgem sha512_expand
.purgem sha512_round
.purgem sha512_rounds
.purgem sha512_prefix
.purgem sha512_full_row
.purgem sha512_tail_row
.popsection

.pushsection .rodata.ed25519_simd_sha512_challenge,"a",@progbits
.p2align 6
.Lsha_swap:
.rept 4
    .byte 7,6,5,4,3,2,1,0, 15,14,13,12,11,10,9,8
.endr
.Lsha_prefix_bytes:
    .quad 64
.Lsha_last_bias:
    .quad 80
.p2align 6
.Lsha_iv:
    .quad 0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1
    .quad 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179
.p2align 6
.Lsha_k:
    .quad 0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc
    .quad 0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118
    .quad 0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2
    .quad 0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694
    .quad 0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65
    .quad 0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5
    .quad 0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4
    .quad 0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70
    .quad 0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df
    .quad 0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b
    .quad 0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30
    .quad 0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8
    .quad 0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8
    .quad 0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3
    .quad 0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec
    .quad 0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b
    .quad 0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178
    .quad 0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b
    .quad 0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c
    .quad 0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817
.Lsha_k_end:
.popsection
