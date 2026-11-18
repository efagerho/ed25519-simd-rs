.intel_syntax noprefix
.text
.global probe, probe_end, capture
.hidden probe, probe_end
probe:
    call .Ldecrement
    jne .Ltaken
    mov eax, 0
    ret
.Ltaken:
    mov eax, 1
    ret
.Ldecrement:
    dec ecx
    ret
probe_end:

# SysV capture(initial_rcx, result). Record both register values and the
# zero flag before the comparison of the caller's stack pointer changes it.
capture:
    mov r9, rsp
    mov rcx, rdi
    call probe
    setz r8b
    movzx r8d, r8b
    cmp rsp, r9
    jne .Lbad_stack
    mov [rsi], rax
    mov [rsi+8], rcx
    mov [rsi+16], r8
    ret
.Lbad_stack:
    ud2
.section .note.GNU-stack,"",@progbits
