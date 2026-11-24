// SysV AMD64: (BatchInput *rows, usize count, bool *out, ChunkScratch *scratch,
//              PointTable *identity, BasepointTableEntries *base).
// Rows are in processing order. Each names a readable key, signature, message
// and its original output index. The output has count bytes and scratch is
// 64-byte aligned. Both must be disjoint from each other and all inputs.
// Return 1 on completion (including an empty batch), 0 on a bad output index.
//
// Stack offsets below are shared by both policy instantiations. Preparation
// and scoring both take eight table pointers as the first field of their ABI.
// Reuse those pointers in place after saving the validity bytes.
.equ .Lvb_digest,   0                 // 512 bytes, word-major
.equ .Lvb_keys,     512               // ChunkInputs: keys, then signatures
.equ .Lvb_sigs,     576
.equ .Lvb_messages, 640
.equ .Lvb_lengths,  704
.equ .Lvb_tables,   768               // PreparedLanes, then post-hash Inputs
.equ .Lvb_lanes,    856               // PendingLanes: valid, indices, active
.equ .Lvb_indices,  .Lvb_lanes + 8
.equ .Lvb_active,   .Lvb_lanes + 72
.equ .Lvb_identity, 936
.equ .Lvb_base,     944
.equ .Lvb_frame,    960

.macro verify_batch name, prepare, decoded
.pushsection .text.\name,"ax",@progbits
.p2align 4
.globl \name
.hidden \name
.type \name,@function
\name:
    test rsi, rsi
    jz .Lvb_empty\@
    push rbx
    push r12
    push r13
    push r14
    push r15
    sub rsp, .Lvb_frame               // 16-byte aligned at each call
    mov rbx, rdi                      // next row
    mov r12, rsi                      // remaining
    mov r13, rsi                      // total output length
    mov r14, rdx                      // output bytes
    mov r15, rcx                      // reusable chunk scratch
    mov [rsp + .Lvb_identity], r8
    mov [rsp + .Lvb_base], r9
.Lvb_chunk\@:
    cmp r12, 8
    jb .Lvb_tail\@
    mov qword ptr [rsp + .Lvb_active], 8
    sub r12, 8
.Lvb_stage\@:
    // Each half-register holds one row's key, signature, message and length.
    vmovdqu ymm0, [rbx + 40*0]
    vmovdqu ymm1, [rbx + 40*1]
    vmovdqu ymm2, [rbx + 40*4]
    vmovdqu ymm3, [rbx + 40*5]
    vinserti64x4 zmm0, zmm0, [rbx + 40*2], 1
    vinserti64x4 zmm1, zmm1, [rbx + 40*3], 1
    vinserti64x4 zmm2, zmm2, [rbx + 40*6], 1
    vinserti64x4 zmm3, zmm3, [rbx + 40*7], 1
    // Interleave adjacent rows, then select the four even or odd 128-bit pairs.
    vpunpcklqdq zmm4, zmm0, zmm1
    vpunpckhqdq zmm5, zmm0, zmm1
    vpunpcklqdq zmm6, zmm2, zmm3
    vpunpckhqdq zmm7, zmm2, zmm3
    vshufi64x2 zmm0, zmm4, zmm6, 0x88
    vshufi64x2 zmm1, zmm5, zmm7, 0x88
    vshufi64x2 zmm2, zmm4, zmm6, 0xdd
    vshufi64x2 zmm3, zmm5, zmm7, 0xdd
    vmovdqu64 [rsp + .Lvb_keys], zmm0
    vmovdqu64 [rsp + .Lvb_sigs], zmm1
    vmovdqu64 [rsp + .Lvb_messages], zmm2
    vmovdqu64 [rsp + .Lvb_lengths], zmm3
.irp i,0,1,2,3,4,5,6,7
    mov rax, [rbx + 40*\i + 32]
    mov [rsp + .Lvb_indices + 8*\i], rax
.endr
    add rbx, 320
    mov rdi, r15
    lea rsi, [rsp + .Lvb_keys]
    mov rdx, [rsp + .Lvb_identity]
    lea rcx, [rsp + .Lvb_tables]
    call \prepare
    test eax, eax
    jz .Lvb_reject\@

    // Scatter always rejects ineligible lanes. Hash an empty message in
    // those lanes so they cannot extend the SIMD hash loop.
    vpmovzxbq zmm0, qword ptr [rsp + .Lvb_tables + 64]
    vptestmq k1, zmm0, zmm0
    vmovdqu64 zmm0{k1}{z}, [rsp + .Lvb_lengths]
    vmovdqu64 [rsp + .Lvb_lengths], zmm0
    lea rdi, [rsp + .Lvb_digest]
    lea rsi, [r15 + 256]              // original R encodings
    mov rdx, r15                      // original key encodings
    lea rcx, [rsp + .Lvb_messages]
    lea r8, [rsp + .Lvb_lengths]
    call ed25519_simd_sha512_challenge

    lea rdi, [rsp + .Lvb_tables]
    mov rax, [rdi + 64]
    mov [rsp + .Lvb_lanes], rax
    movzx edx, byte ptr [rdi + 72]    // R-valid mask
    mov rax, [rsp + .Lvb_base]
    mov [rdi + 64], rax
    lea rax, [r15 + 512]              // signed S digits
    mov [rdi + 72], rax
    lea rax, [rsp + .Lvb_digest]
    mov [rdi + 80], rax
    lea rsi, [r15 + 2304]             // decoded affine R
    lea rcx, [rsp + .Lvb_lanes]
    mov r8, r14
    mov r9, r13
    call \decoded
    jmp .Lvb_next\@

.Lvb_reject\@:
    // Preparation may have left partial outputs. Scatter zeros using only
    // the indices and active count recorded before preparation.
    mov qword ptr [rsp + .Lvb_lanes], 0
    lea rdi, [rsp + .Lvb_lanes]
    mov rsi, r14
    mov rdx, r13
    xor eax, eax
    call ed25519_simd_zip215_scatter
.Lvb_next\@:
    test eax, eax
    jz .Lvb_done\@
    test r12, r12
    jnz .Lvb_chunk\@
.Lvb_done\@:
    add rsp, .Lvb_frame
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    ret
.Lvb_empty\@:
    mov eax, 1
    ret
.Lvb_tail\@:
    // Pad the last chunk to eight rows, repeating the last live record.
    // The digest buffer is free until the call to SHA-512.
    mov [rsp + .Lvb_active], r12
    mov rsi, rbx
    lea rax, [r12 + 4*r12]
    lea rdi, [rbx + 8*rax - 40]
    lea rbx, [rsp + .Lvb_digest]
    xor r12d, r12d
    xor ecx, ecx
.Lvb_pad\@:
    vmovdqu ymm0, [rsi]
    mov rax, [rsi + 32]
    vmovdqu [rbx + rcx], ymm0
    mov [rbx + rcx + 32], rax
    lea rax, [rsi + 40]
    cmp rsi, rdi
    cmovb rsi, rax
    add ecx, 40
    cmp ecx, 320
    jne .Lvb_pad\@
    jmp .Lvb_stage\@
.size \name,.-\name
.popsection
.endm

verify_batch ed25519_simd_zip215_verify_batch, ed25519_simd_prepare_chunk, ed25519_simd_zip215_decoded
verify_batch ed25519_simd_dalek_verify_batch, ed25519_simd_dalek_prepare_chunk, ed25519_simd_dalek_decoded
.purgem verify_batch
