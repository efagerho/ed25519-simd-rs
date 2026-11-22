// SysV AMD64 chunk preparation. RDI = 64-byte-aligned ChunkScratch,
// RSI = eight key pointers then eight signature pointers, RDX = identity PointTable,
// RCX = PreparedLanes. The read-only inputs may repeat. The two outputs,
// stack and read-only inputs must be disjoint. Layouts are in prepare.rs.
// Return 1 if any lane is eligible. On 0 the caller discards both outputs.
.equ .Lpc_keys,       0
.equ .Lpc_r_bytes,  256
.equ .Lpc_digits,   512
.equ .Lpc_points,  1024             // two consecutive WidePoints: A then R
.equ .Lpc_tables,  3584
.equ .Lpc_stride,  2720             // seventeen 160-byte cached points
.equ .Lpc_valid,     64             // after eight selected table pointers
.equ .Lpc_r_valid,   72

.pushsection .text.ed25519_simd_prepare_chunk,"ax",@progbits
.p2align 4
.globl ed25519_simd_prepare_chunk
.hidden ed25519_simd_prepare_chunk
.type ed25519_simd_prepare_chunk,@function
ed25519_simd_prepare_chunk:
    push rbx
    push r12
    push r13
    push r14
    push r15
    sub rsp, 64                     // eight S pointers, stack aligned for calls
    mov rbx, rdi
    mov r12, rdx
    mov r13, rcx
    mov r15, rsi

    mov eax, 32                     // S starts 32 bytes into each signature
    vpbroadcastq zmm0, rax
    vpaddq zmm0, zmm0, [rsi + 64]
    vmovdqu64 [rsp], zmm0
    lea rdi, [rbx + .Lpc_digits]
    mov rsi, rsp
    call ed25519_simd_prepare_signature_scalars
    test eax, eax
    jz .Lpc_done
    mov r14d, eax

    xor ecx, ecx
.Lpc_encodings:
    mov rdi, [r15]
    mov rsi, [r15 + 64]
    vmovdqu ymm0, [rdi]
    vmovdqu ymm1, [rsi]
    vmovdqa [rbx + rcx + .Lpc_keys], ymm0
    vmovdqa [rbx + rcx + .Lpc_r_bytes], ymm1
    add r15, 8
    add ecx, 32
    cmp ecx, 256
    jne .Lpc_encodings
    lea rdi, [rbx + .Lpc_points]
    lea rsi, [rbx + .Lpc_keys]
    mov edx, 2
    call ed25519_simd_zip215_decode_r
    movzx r15d, al                  // A decode mask
    shr eax, 8
    mov [r13 + .Lpc_r_valid], al    // R decode mask used by the post-hash check
    and r14d, r15d                  // canonical S and decodable A
    jz .Lpc_rejected

    lea rdi, [rbx + .Lpc_points]    // builder mutates A; R stays in place
    lea rsi, [rbx + .Lpc_tables]
    mov edx, 8
    call ed25519_simd_build_key_tables

    // The decoder mask selects the computed table address or the identity.
    vpbroadcastq zmm0, rbx
    vpmovzxwq zmm1, [rip + .Lpc_table_offsets]
    vpbroadcastq zmm2, r12
    kmovw k1, r15d
    vpaddq zmm2{k1}, zmm0, zmm1
    vmovdqu64 [r13], zmm2

    // Expand the eligibility bits to the eight canonical Rust bool bytes.
    kmovw k1, r14d
    vpmovm2b zmm0, k1
    vpabsb zmm0, zmm0
    vmovq [r13 + .Lpc_valid], xmm0
    vzeroupper
    mov eax, 1
    jmp .Lpc_done
.Lpc_rejected:
    xor eax, eax
.Lpc_done:
    add rsp, 64
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    ret
.type .Lpc_table_offsets,@object
.Lpc_table_offsets:
.irp lane,0,1,2,3,4,5,6,7
    .short .Lpc_tables + \lane * .Lpc_stride
.endr
.size ed25519_simd_prepare_chunk, .-ed25519_simd_prepare_chunk
.popsection

.pushsection .text.ed25519_simd_dalek_prepare_chunk,"ax",@progbits
.p2align 4
.globl ed25519_simd_dalek_prepare_chunk
.hidden ed25519_simd_dalek_prepare_chunk
.type ed25519_simd_dalek_prepare_chunk,@function
ed25519_simd_dalek_prepare_chunk:
    push rbx
    mov rbx, rcx
    call ed25519_simd_prepare_chunk
    test eax, eax
    jz .Lpc_dalek_done
    mov rdi, rbx
    lea rsi, [rbx + .Lpc_valid]
    call ed25519_simd_dalek_filter_keys
    xor eax, eax
    cmp qword ptr [rbx + .Lpc_valid], 0
    setne al
.Lpc_dalek_done:
    pop rbx
    ret
.size ed25519_simd_dalek_prepare_chunk, .-ed25519_simd_dalek_prepare_chunk
.popsection
