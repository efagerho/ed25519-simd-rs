.intel_syntax noprefix
.text
.global probe, probe_end
.hidden probe, probe_end
probe:
    movzx eax, word ptr [rdi+1]
    mov r11d, eax
    shr r11d, 4
    and eax, 15
    and r11d, 240
    or eax, r11d
    xor eax, 136
    imul eax, eax, 160
    and eax, 63
    lea rax, [rax+2*rax]
    add rax, [rdi+128]
    vmovdqu64 zmm3, [rdi+rax]
    vmovdqu ymm3, [rdi+rax+8]
    vinserti64x4 zmm18, zmm3, [rdi+rax+31], 1
    vmovdqu64 zmm17, [rdi+rax+32]
    movzx eax, byte ptr [rdi+4]
    and eax, 15
    vinserti64x4 zmm19, zmm17, [rdi+rax+64], 0
    vpunpcklqdq zmm20, zmm18, zmm17
    vpunpckhqdq zmm21, zmm18, zmm17
    vmovdqa64 [rdi+192], zmm20
    vmovdqa64 [rdi+256], zmm21
    vmovdqa64 [rdi+320], zmm3
    vmovdqa64 [rdi+384], zmm19
    vzeroupper
    ret
probe_end:
.section .note.GNU-stack,"",@progbits
