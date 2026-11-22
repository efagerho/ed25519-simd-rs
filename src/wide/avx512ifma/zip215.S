// SysV AMD64. Inputs contains eight table pointers, the affine base table,
// the lane-major S digits and eight SHA-512 digest word rows. All scalars
// and indices are public. The three entries return 1 on success or 0 for
// invalid scatter metadata. Stack scratch and output must be disjoint from
// all input buffers. Layout assertions are in post_hash_asm.rs.

post_candidate ed25519_simd_zip215_candidate, 1

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
    sub rsp, .Lpost_point_size
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

post_push ed25519_simd_zip215_push, ed25519_simd_zip215_candidate, ed25519_simd_zip215_flush

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
    sub rsp, 2 * .Lpost_point_size
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
    lea rdi, [rbx + .Lpost_point_size]
    lea rsi, [rsp + .Lpost_point_size]
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
    mov rax, [rdi + .Lpost_count]
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
    mov qword ptr [rbx + .Lpost_count], 0
    xor eax, eax
    cmp r12, 2
    jb .Lzip_resolve                // a single chunk cannot share an inversion
    // A chunk with any y mismatch needs the full check anyway. Only try
    // sharing an inversion if at least two chunks can avoid decompression.
    // This test chooses a schedule; only the full predicates below score lanes.
    mov rdi, rbx
    lea rsi, [rbx + .Lpost_encodings]
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
    add rdi, .Lpost_point_size
    add rsi, 256
    dec edx
    jnz .Lzip_probe
    xor eax, eax
    jmp .Lzip_resolve
.Lzip_exact:
    mov rdi, rbx
    lea rsi, [rbx + .Lpost_encodings]
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
    imul rdi, r13, .Lpost_point_size
    add rdi, rbx
    mov rsi, r13
    shl rsi, 8
    lea rsi, [rbx + rsi + .Lpost_encodings]
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
    lea rbx, [rbx + .Lpost_lanes]
    xor r13d, r13d
.Lzip_score:
    movzx eax, byte ptr [rsp + r13]
    mov rdi, rbx
    mov rsi, r14
    mov rdx, r15
    call ed25519_simd_zip215_scatter
    test eax, eax
    jz .Lzip_done
    add rbx, .Lpost_lane_size
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
