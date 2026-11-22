// SysV post-hash Dalek verification. The exact equation only consumes XYZ.
post_candidate ed25519_simd_dalek_candidate, 0
// Strict verification rejects y >= p, and points with y = 0 or ±1 have
// order dividing four. These encodings have y in [0,1] or [2^255-20,2^255).
// Check all eight before skipping a candidate. A usual first word falls
// outside both intervals and costs one load and an unsigned range test.
.macro dalek_screen_encodings
    mov eax, [rdx]
    add eax, 20
    cmp eax, 21
    ja .Ldalek_queue
    mov r10, rdx
    lea r11, [rdx + 256]
.Ldalek_encoding:
    mov rax, [r10 + 24]
    cmp qword ptr [r10], 1
    ja .Ldalek_high_y
    shl rax, 1                         // discard the encoded X sign
    or rax, [r10 + 16]
    or rax, [r10 + 8]
    jnz .Ldalek_queue
    jmp .Ldalek_next_encoding
.Ldalek_high_y:
    cmp qword ptr [r10], -20
    jb .Ldalek_queue
    bts rax, 63                        // ignore either X sign
    and rax, [r10 + 16]
    and rax, [r10 + 8]
    cmp rax, -1
    jne .Ldalek_queue
.Ldalek_next_encoding:
    add r10, 32
    cmp r10, r11
    jne .Ldalek_encoding
    xor eax, eax
    mov rdi, rcx
    mov rsi, r8
    mov rdx, r9
    jmp ed25519_simd_zip215_scatter
.Ldalek_queue:
.endm
post_push ed25519_simd_dalek_push, ed25519_simd_dalek_candidate, ed25519_simd_dalek_flush, dalek_screen_encodings
.purgem dalek_screen_encodings

.pushsection .text.ed25519_simd_dalek_flush,"ax",@progbits
.p2align 4
.globl ed25519_simd_dalek_flush
.hidden ed25519_simd_dalek_flush
.type ed25519_simd_dalek_flush,@function
// (queue, output, length). Recompress the occupied prefix with one inversion.
ed25519_simd_dalek_flush:
    mov rax, [rdi + .Lpost_count]
    test rax, rax
    jz .Ldalek_empty
    push rbx
    push r12
    push r13
    push r14
    push r15
    lea rbx, [rdi + .Lpost_lanes]
    mov r12, rsi
    mov r13, rdx
    mov r15, rax
    mov qword ptr [rdi + .Lpost_count], 0
    lea rsi, [rdi + .Lpost_encodings]
    mov rdx, r15
    call ed25519_simd_dalek_recompress
    mov r14, rax
.Ldalek_score:
    movzx eax, r14b
    mov rdi, rbx
    mov rsi, r12
    mov rdx, r13
    call ed25519_simd_zip215_scatter
    test eax, eax
    jz .Ldalek_done
    shr r14, 8
    add rbx, .Lpost_lane_size
    dec r15
    jnz .Ldalek_score
.Ldalek_done:
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    ret
.Ldalek_empty:
    mov eax, 1
    ret
.size ed25519_simd_dalek_flush,.-ed25519_simd_dalek_flush
.popsection

.pushsection .text.ed25519_simd_dalek_decoded,"ax",@progbits
.p2align 4
.globl ed25519_simd_dalek_decoded
.hidden ed25519_simd_dalek_decoded
.type ed25519_simd_dalek_decoded,@function
// (Inputs, decoded affine R, R-valid, PendingLanes, output, length).
ed25519_simd_dalek_decoded:
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
    mov [rsp], rdi                     // Inputs, until the candidate overwrites this slot
    movzx r12d, dl
    mov r13, rcx
    mov r14, r8
    mov r15, r9
    // Keep lanes with an eligible key and a decodable, canonical R.
    vmovq xmm0, [rcx]
    vptestmb k1, zmm0, zmm0
    kmovw eax, k1
    and r12d, eax
    jz .Ldalek_no_match
    // The decoder leaves the original five radix-51 digits in affine Y.
    fe51_load rbx, 320
    vpbroadcastq zmm29, qword ptr [rip + .Ltor_limb_mask]
    fe51_high_ones
    vpcmpuq k2{k1}, zmm0, qword ptr [rip + .Lfe51_p0]{1to8}, 5
    kmovw eax, k2
    not eax
    and r12d, eax
    jz .Ldalek_no_match
    // x=0 implies y=+1 or -1, so this also rejects both negative zeros.
    mov rdi, rbx
    call ed25519_simd_small_order_ifma
    not eax
    and r12d, eax
    jz .Ldalek_no_match

    mov rsi, [rsp]
    mov rdi, rsp
    call ed25519_simd_dalek_candidate
    mov rdi, rsp
    fe51_constants
    fe51_load rbx, 320
    fe51_match_projective_y rdi
    kmovw eax, k1
    and r12d, eax
    jz .Ldalek_no_match
    // The decoder selected affine X using the sign in the original bytes.
    fe51_load rbx, 0
    fe51_match_coordinate rdi, 0
    kmovw eax, k1
    and eax, r12d
    jmp .Ldalek_scatter
.Ldalek_no_match:
    xor eax, eax
.Ldalek_scatter:
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
.size ed25519_simd_dalek_decoded,.-ed25519_simd_dalek_decoded
.popsection

.pushsection .text.ed25519_simd_dalek_filter_keys,"ax",@progbits
.p2align 4
.globl ed25519_simd_dalek_filter_keys
.hidden ed25519_simd_dalek_filter_keys
.type ed25519_simd_dalek_filter_keys,@function
// (eight CachedPoint table pointers, eight writable eligibility bools).
// Entry 16 represents [8]A. It is the identity exactly when Y+X = Y-X
// and (Y-X)+(Y-X) = 2Z modulo p. Check the second equality only for ties.
ed25519_simd_dalek_filter_keys:
    sub rsp, 8
    vmovdqu64 zmm20, [rdi]
    fe51_constants
.macro dalek_column i, saved, bias
    kxnorw k3, k3, k3
    vpgatherqq zmm\saved{k3}, [zmm20 + 16*160 + 8*\i]
    kxnorw k3, k3, k3
    vpgatherqq zmm\i{k3}, [zmm20 + 16*160 + 40 + 8*\i]
    vpaddq zmm\i, zmm\i, zmm\bias
    vpsubq zmm\i, zmm\i, zmm\saved
.endm
    dalek_column 0, 15, 30
    dalek_column 1, 16, 31
    dalek_column 2, 17, 31
    dalek_column 3, 18, 31
    dalek_column 4, 19, 31
    call .Lfe51_carry
    fe51_high_ones
    vpcmpeqq k1{k1}, zmm0, qword ptr [rip + .Lfe51_p0]{1to8}
    kortestw k1, k1
    jz .Ldalek_keys_done
    kmovw ecx, k1
.macro dalek_z i, saved, bias
    kxnorw k3, k3, k3
    vpgatherqq zmm10{k3}, [zmm20 + 16*160 + 120 + 8*\i]
    vpaddq zmm\i, zmm\saved, zmm\saved
    vpaddq zmm\i, zmm\i, zmm\bias
    vpsubq zmm\i, zmm\i, zmm10
.endm
    dalek_z 0, 15, 30
    dalek_z 1, 16, 31
    dalek_z 2, 17, 31
    dalek_z 3, 18, 31
    dalek_z 4, 19, 31
    call .Lfe51_carry
    fe51_high_ones
    vpcmpeqq k1{k1}, zmm0, qword ptr [rip + .Lfe51_p0]{1to8}
    kmovw k2, ecx
    kandw k1, k1, k2
    vpmovm2b zmm0, k1
    vmovq xmm1, [rsi]
    vpandn xmm0, xmm0, xmm1
    vmovq [rsi], xmm0
.Ldalek_keys_done:
    add rsp, 8
    vzeroupper
    ret
.size ed25519_simd_dalek_filter_keys,.-ed25519_simd_dalek_filter_keys
.popsection
