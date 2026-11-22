// Standalone post-hash queue layout shared by the two assembly policies.
// Each occupied slot owns its candidate, original encodings and scatter indices.
.equ .Lpost_chunks, 8
.equ .Lpost_point_size, 1280
.equ .Lpost_lane_size, 80
.equ .Lpost_encodings, .Lpost_chunks * .Lpost_point_size
.equ .Lpost_lanes, .Lpost_encodings + .Lpost_chunks * 256
.equ .Lpost_count, .Lpost_lanes + .Lpost_chunks * .Lpost_lane_size

.macro post_candidate name, full
.pushsection .text.\name,"ax",@progbits
.p2align 4

// RDI = aligned WidePoint output, RSI = borrowed Inputs.
.type \name,@function
\name:
    push rbx
    push r12
    sub rsp, 520                        // 512 digit bytes, 16-byte call alignment
    mov rbx, rdi
    mov r12, rsi
    mov rdi, rsp
    mov rsi, [r12 + 80]
    call ed25519_simd_digest_to_radix16
    mov rdi, rbx
    mov rsi, r12
    mov rdx, [r12 + 64]
    mov rcx, [r12 + 72]
    mov r8, rsp
    .if \full
        mov r9d, 1
    .else
        xor r9d, r9d
    .endif
    call ed25519_simd_mul_s_base_minus_k_public
    add rsp, 520
    pop r12
    pop rbx
    ret

.size \name,.-\name
.popsection
.endm

.pushsection .text.ed25519_simd_zip215_scatter,"ax",@progbits
.p2align 4
// EAX holds the policy acceptance mask. RDI = PendingLanes, RSI = output, RDX = length.
// Write exactly the active lanes. In particular, repeated indices used to
// pad the last SIMD chunk cannot overwrite a real signature's result.
.type ed25519_simd_zip215_scatter,@function
ed25519_simd_zip215_scatter:
    mov rcx, [rdi + 72]
    cmp rcx, 8
    ja .Lzip_bad
    xor r8d, r8d
    test rcx, rcx
    jz .Lzip_ok
.Lzip_lane:
    mov r9, [rdi + 8 + 8*r8]
    cmp r9, rdx
    jae .Lzip_bad
    mov r10b, [rdi + r8]               // valid is a Rust bool (0 or 1)
    and r10b, al
    mov [rsi + r9], r10b
    shr eax, 1
    inc r8
    cmp r8, rcx
    jb .Lzip_lane
.Lzip_ok:
    mov eax, 1
    ret
.Lzip_bad:
    xor eax, eax
    ret

.size ed25519_simd_zip215_scatter,.-ed25519_simd_zip215_scatter
.popsection

.macro post_push name, candidate, flush, screen=
.pushsection .text.\name,"ax",@progbits
// (queue, Inputs, encoded R chunk, PendingLanes, output, length).
// Compute the candidate while the key tables are still borrowed.
.p2align 4
.globl \name
.hidden \name
.type \name,@function
\name:
    .ifnb \screen
        \screen
    .endif
    push rbx
    push r12
    push r13
    mov rbx, rdi
    mov r12, r8
    mov r13, r9
    mov rax, [rbx + .Lpost_count]
    mov r8, rax
    shl r8, 8
.irp offset,0,64,128,192
    vmovdqu64 zmm0, [rdx + \offset]
    vmovdqa64 [rbx + r8 + .Lpost_encodings + \offset], zmm0
.endr
    imul r8, rax, .Lpost_lane_size
    vmovdqu64 zmm0, [rcx]
    vmovdqu xmm1, [rcx + 64]
    vmovdqu64 [rbx + r8 + .Lpost_lanes], zmm0
    vmovdqu [rbx + r8 + .Lpost_lanes + 64], xmm1
    imul rdi, rax, .Lpost_point_size
    add rdi, rbx
    call \candidate
    mov rax, [rbx + .Lpost_count]
    inc eax
    mov [rbx + .Lpost_count], rax
    cmp eax, .Lpost_chunks
    mov rdi, rbx
    mov rsi, r12
    mov rdx, r13
    pop r13
    pop r12
    pop rbx
    je \flush
    mov eax, 1
    ret
.size \name,.-\name

.popsection
.endm
