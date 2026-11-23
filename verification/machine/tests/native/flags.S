.intel_syntax noprefix
.text
.global probe,probe_end,capture
.hidden probe,probe_end
probe:
    mov eax,0
    test ecx,3
    je .Lexit
    cmp edx,-1
    je .Lone
    test edx,1
    je .Lexit
    cmp ecx,4
.Lexit:
    jmp .Lnear
    nop
    nop
.Lone:
    mov eax,1
.Lret:
    ret
.Lnear:
    .byte 0xe9
    .long .Lret - . - 4
probe_end:
capture:
    mov rcx,rdi
    mov rdx,rdi
    call probe
    setz dl
    movzx edx,dl
    mov [rsi],rax
    mov [rsi+8],rdx
    ret
.section .note.GNU-stack,"",@progbits
