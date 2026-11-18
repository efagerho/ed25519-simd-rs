.intel_syntax noprefix
.text
.global probe, probe_end, capture
.hidden probe, probe_end
probe:
.Lloop:
    vmovdqu64 zmm0, zmmword ptr [rdi + 64]
    vpaddq zmm31, zmm0, zmm31
    vpmadd52luq zmm31, zmm31, zmm17
    vmovdqu64 zmmword ptr [rdi + 64], zmm31
    dec ecx
    vpaddq zmm2, zmm2, zmm31
    jne .Lloop
    vmovdqu64 zmm1, zmmword ptr [rdi + 64]
    ret
probe_end:

# SysV capture(cells, registers, iterations, status). Save the loop's final
# flag before checking the stack. RDI points eight bytes past a 64-byte boundary.
capture:
    sub rsp, 8
    mov r9, rsp
    mov r8, rcx
    mov rcx, rdx
.irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
    vmovdqu64 zmm\r, [rsi + 64*\r]
.endr
    call probe
    setz al
    movzx eax, al
    cmp rsp, r9
    jne .Lbad_stack
    mov [r8], rcx
    mov [r8 + 8], rax
.irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
    vmovdqu64 [rsi + 64*\r], zmm\r
.endr
    vzeroupper
    add rsp, 8
    ret
.Lbad_stack:
    ud2
.section .note.GNU-stack,"",@progbits
