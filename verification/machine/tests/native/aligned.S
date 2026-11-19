.intel_syntax noprefix
.text
.global probe, probe_end, capture
.hidden probe, probe_end
probe:
    push rbp
    mov rbp, rsp
    and rsp, -64
    sub rsp, 1280
    mov rsi, rsp
    movabs rax, 0xfedcba9876543210
    vpbroadcastq zmm20, rax
    vmovdqu64 [rsi + 640], zmm20
    vmovdqu64 [rsi], zmm20
    lea r8, [rsi + 640]
    vmovdqu64 zmm21, [r8]
    call .Lmiddle
    mov rsp, rbp
    pop rbp
    vzeroupper
    ret
.Lmiddle:
    call .Lleaf
    ret
.Lleaf:
    vmovdqu64 [rdi], zmm21
    ret
probe_end:

# capture(out, registers, status, aligned_frame_base, seed)
# Isolate the host stack; probe has the same aligned frame and nesting as double4.
capture:
    push rbp
    push r12
    push r13
    mov r12, rsi
    mov r11, rdx
    mov r9, rcx
    mov r13, r8
    mov r10, rsp
.irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
    vmovdqu64 zmm\r, [r12 + 64*\r]
.endr
    mov rax, r13
    and eax, 3
    shl rax, 4
    lea rsp, [r9 + 1296]
    add rsp, rax
    mov rbp, r13
    call probe
    mov [r11], rbp
    mov rax, rsp
    sub rax, r9
    mov [r11 + 8], rax
    mov rax, rsi
    sub rax, r9
    mov [r11 + 16], rax
    mov rax, r8
    sub rax, r9
    mov [r11 + 24], rax
    mov rsp, r10
.irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
    vmovdqu64 [r12 + 64*\r], zmm\r
.endr
    vzeroupper
    pop r13
    pop r12
    pop rbp
    ret
.section .note.GNU-stack,"",@progbits
