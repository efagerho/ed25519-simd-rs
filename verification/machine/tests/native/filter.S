.intel_syntax noprefix
.text
.global probe, probe_end
.hidden probe, probe_end
probe:
    vmovdqu64 zmm25, [rdi]
    vmovdqu64 zmm3, [rsi]
    vpmullq zmm18, zmm25, qword ptr [rip + .Lthree]{1to8}
    vpminuq zmm17, zmm18, zmm3
    vpcmpuq k4, zmm17, qword ptr [rip + .Llimit]{1to8}, 1
    kortestw k4, k4
    jne .Lnonzero
    xor eax, eax
    {disp32} jmp .Lreturn
.Lnonzero:
    kmovw eax, k4
.Lreturn:
    ret
.Lthree: .quad 3
.Llimit: .quad 0x8000000000000001
probe_end:
.section .note.GNU-stack,"",@progbits
