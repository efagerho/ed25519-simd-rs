.intel_syntax noprefix
.text
.global probe, probe_end, capture
.hidden probe, probe_end
probe:
    sub rsp, 1928
    movabs rax, 0xfedcba9876543210
    vpbroadcastq zmm29, rax
    mov eax, 19
    vpbroadcastq zmm28, rax
    mov ecx, 0xffffffff
    vmovdqu64 zmm16, [rsi]
    vmovdqu64 zmm17, [rsi + 64]
    vmovdqu64 zmm18, [rdx]
    vmovdqu64 zmm19, [rdx + 64]
    vmovdqu64 [rsp], zmm17
    vmovdqu64 [rsp + 640], zmm19
    lea r8, [rsp]
    vmovdqu64 zmm20, [r8]
    lea r8, [rsp + 640]
    vmovdqu64 zmm21, [r8]
    vmovdqu64 zmm22, [rsp]
    vmovdqu64 zmm23, [rsp + 640]
    vmovdqu64 [rdi], zmm20
    vmovdqu64 [rdi + 64], zmm21
    add rsp, 1928
    vzeroupper
    ret
probe_end:

# SysV capture(out, a, b, registers, status, frame_base).
# The caller owns the test stack and inspects it after the call. Keep
# the host stack and the two snapshot pointers outside the probe registers.
capture:
    push r12
    mov r12, rcx
    mov r11, r8
    mov r10, rsp
.irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
    vmovdqu64 zmm\r, [r12 + 64*\r]
.endr
    lea rsp, [r9 + 1936]
    mov rcx, -1
    call probe
    mov [r11], rax
    mov [r11 + 8], rcx
    lea rax, [r9 + 1936]
    cmp rsp, rax
    mov rsp, r10
    jne .Lbad_stack
    sub r8, r9
    mov [r11 + 16], r8
.irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
    vmovdqu64 [r12 + 64*\r], zmm\r
.endr
    vzeroupper
    pop r12
    ret
.Lbad_stack:
    ud2
.section .note.GNU-stack,"",@progbits
