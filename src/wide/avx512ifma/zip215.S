// SysV AMD64. Inputs contains eight table pointers, the affine base table,
// the lane-major S digits and eight SHA-512 digest word rows. All scalars
// and indices are public. The three entries return 1 on success or 0 for
// invalid scatter metadata. Stack scratch and output must be disjoint from
// all input buffers. Layout assertions are in zip215_asm.rs.
// Separate arrays let both recompression and decoding read contiguous chunks.
.equ .Lzip_chunks, 8
.equ .Lzip_point_size, 1280
.equ .Lzip_lane_size, 80
.equ .Lzip_encodings, .Lzip_chunks * .Lzip_point_size
.equ .Lzip_lanes, .Lzip_encodings + .Lzip_chunks * 256
.equ .Lzip_count, .Lzip_lanes + .Lzip_chunks * .Lzip_lane_size

.pushsection .text.ed25519_simd_zip215_candidate,"ax",@progbits
.p2align 4

// RDI = aligned, uninitialized WidePoint; RSI = borrowed Inputs.
// Compute Q = [s]B - [k]A with T, which the cofactor check consumes.
.type ed25519_simd_zip215_candidate,@function
ed25519_simd_zip215_candidate:
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
    mov r9d, 1
    call ed25519_simd_mul_s_base_minus_k_public
    add rsp, 520
    pop r12
    pop rbx
    ret

.size ed25519_simd_zip215_candidate,.-ed25519_simd_zip215_candidate
.popsection

.pushsection .text.ed25519_simd_zip215_scatter,"ax",@progbits
.p2align 4
// EAX holds equation & R-valid. RDI = PendingLanes, RSI = output, RDX = length.
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

.pushsection .text.ed25519_simd_zip215_decoded,"ax",@progbits
// (Inputs, decoded affine R, R-valid mask, PendingLanes, output, length).
.p2align 4
.globl ed25519_simd_zip215_decoded
.hidden ed25519_simd_zip215_decoded
.type ed25519_simd_zip215_decoded,@function
ed25519_simd_zip215_decoded:
    push rbp
    mov rbp, rsp
    push rbx
    push r12
    push r13
    push r14
    push r15
    and rsp, -64
    sub rsp, .Lzip_point_size
    mov rbx, rsi
    movzx r12d, dl
    mov r13, rcx
    mov r14, r8
    mov r15, r9
    mov rsi, rdi
    mov rdi, rsp
    call ed25519_simd_zip215_candidate
    mov rdi, rsp
    mov rsi, rbx
    call ed25519_simd_check_8_torsion_ifma
    and eax, r12d
    mov rdi, r13
    mov rsi, r14
    mov rdx, r15
    lea rsp, [rbp - 40]
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    pop rbp
    jmp ed25519_simd_zip215_scatter
.size ed25519_simd_zip215_decoded,.-ed25519_simd_zip215_decoded

.popsection

.pushsection .text.ed25519_simd_zip215_push,"ax",@progbits
// (queue, Inputs, encoded R chunk, PendingLanes, output, length).
// Compute the candidate while the key tables are still borrowed.
.p2align 4
.globl ed25519_simd_zip215_push
.hidden ed25519_simd_zip215_push
.type ed25519_simd_zip215_push,@function
ed25519_simd_zip215_push:
    push rbx
    push r12
    push r13
    mov rbx, rdi
    mov r12, r8
    mov r13, r9
    mov rax, [rbx + .Lzip_count]
    mov r8, rax
    shl r8, 8
.irp offset,0,64,128,192
    vmovdqu64 zmm0, [rdx + \offset]
    vmovdqa64 [rbx + r8 + .Lzip_encodings + \offset], zmm0
.endr
    imul r8, rax, .Lzip_lane_size
    vmovdqu64 zmm0, [rcx]
    vmovdqu xmm1, [rcx + 64]
    vmovdqu64 [rbx + r8 + .Lzip_lanes], zmm0
    vmovdqu [rbx + r8 + .Lzip_lanes + 64], xmm1
    imul rdi, rax, .Lzip_point_size
    add rdi, rbx
    call ed25519_simd_zip215_candidate
    mov rax, [rbx + .Lzip_count]
    inc eax
    mov [rbx + .Lzip_count], rax
    cmp eax, .Lzip_chunks
    mov rdi, rbx
    mov rsi, r12
    mov rdx, r13
    pop r13
    pop r12
    pop rbx
    je ed25519_simd_zip215_flush
    mov eax, 1
    ret
.size ed25519_simd_zip215_push,.-ed25519_simd_zip215_push

.popsection

.pushsection .text.ed25519_simd_zip215_check_r,"ax",@progbits
.p2align 4
// RDI = one or two candidates, RSI = their encodings, RDX = count.
// EAX returns a ZIP-215 acceptance byte per chunk. EDX returns the count.
.type ed25519_simd_zip215_check_r,@function
ed25519_simd_zip215_check_r:
    push rbp
    mov rbp, rsp
    push rbx
    push r12
    push r13
    and rsp, -64
    sub rsp, 2 * .Lzip_point_size
    mov rbx, rdi
    mov r12d, edx
    mov rdi, rsp
    call ed25519_simd_zip215_decode_r
    mov r13d, eax
    mov rdi, rbx
    mov rsi, rsp
    call ed25519_simd_check_8_torsion_ifma
    and r13b, al
    cmp r12d, 1
    je .Lzip_checked
    lea rdi, [rbx + .Lzip_point_size]
    lea rsi, [rsp + .Lzip_point_size]
    call ed25519_simd_check_8_torsion_ifma
    movzx eax, al
    shl eax, 8
    or eax, 255
    and r13d, eax
.Lzip_checked:
    mov eax, r13d
    mov edx, r12d
    lea rsp, [rbp - 24]
    pop r13
    pop r12
    pop rbx
    pop rbp
    ret
.size ed25519_simd_zip215_check_r,.-ed25519_simd_zip215_check_r
.popsection

.pushsection .text.ed25519_simd_zip215_flush,"ax",@progbits
.p2align 4
// (queue, output, length). Canonical equality implies [8](Q-R)=0.
// An unset recompression bit is inconclusive under ZIP-215: resolve those
// chunks by decoding R and checking the cofactored equation.
.globl ed25519_simd_zip215_flush
.hidden ed25519_simd_zip215_flush
.type ed25519_simd_zip215_flush,@function
ed25519_simd_zip215_flush:
    mov rax, [rdi + .Lzip_count]
    test rax, rax
    jnz .Lzip_nonempty
    mov eax, 1
    ret
.Lzip_nonempty:
    push rbx
    push r12
    push r13
    push r14
    push r15
    sub rsp, 16
    mov rbx, rdi
    mov r12, rax
    mov r14, rsi
    mov r15, rdx
    mov qword ptr [rbx + .Lzip_count], 0
    xor eax, eax
    cmp r12, 2
    jb .Lzip_resolve                // a single chunk cannot share an inversion
    // A chunk with any y mismatch needs the full check anyway. Only try
    // sharing an inversion if at least two chunks can avoid decompression.
    // This test chooses a schedule; only the full predicates below score lanes.
    mov rdi, rbx
    lea rsi, [rbx + .Lzip_encodings]
    mov rdx, r12
    mov ecx, 2
    fe51_constants
.Lzip_probe:
    encoded_point_words rsi
    encoded_y_limbs
    fe51_match_projective_y rdi
    kmovw eax, k1
    cmp al, 255
    jne .Lzip_probe_next
    dec ecx
    jz .Lzip_exact
.Lzip_probe_next:
    add rdi, .Lzip_point_size
    add rsi, 256
    dec edx
    jnz .Lzip_probe
    xor eax, eax
    jmp .Lzip_resolve
.Lzip_exact:
    mov rdi, rbx
    lea rsi, [rbx + .Lzip_encodings]
    mov rdx, r12
    call ed25519_simd_dalek_recompress
.Lzip_resolve:
    mov [rsp], rax
    xor r13d, r13d
.Lzip_chunk:
    cmp byte ptr [rsp + r13], 255
    je .Lzip_next
    // Decode adjacent unresolved chunks together. Exactly matching chunks
    // and the end of the queue leave a single chunk for the decoder.
    mov edx, 1
    lea rcx, [r13 + 1]
    cmp rcx, r12
    jae .Lzip_check
    cmp byte ptr [rsp + rcx], 255
    je .Lzip_check
    inc edx
.Lzip_check:
    imul rdi, r13, .Lzip_point_size
    add rdi, rbx
    mov rsi, r13
    shl rsi, 8
    lea rsi, [rbx + rsi + .Lzip_encodings]
    call ed25519_simd_zip215_check_r
    cmp edx, 2
    je .Lzip_save_pair
    mov [rsp + r13], al
    jmp .Lzip_next
.Lzip_save_pair:
    mov [rsp + r13], ax
    inc r13
.Lzip_next:
    inc r13
    cmp r13, r12
    jb .Lzip_chunk
    lea rbx, [rbx + .Lzip_lanes]
    xor r13d, r13d
.Lzip_score:
    movzx eax, byte ptr [rsp + r13]
    mov rdi, rbx
    mov rsi, r14
    mov rdx, r15
    call ed25519_simd_zip215_scatter
    test eax, eax
    jz .Lzip_done
    add rbx, .Lzip_lane_size
    inc r13
    cmp r13, r12
    jb .Lzip_score
.Lzip_done:
    add rsp, 16
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    ret
.size ed25519_simd_zip215_flush,.-ed25519_simd_zip215_flush
.popsection
