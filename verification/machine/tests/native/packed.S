.intel_syntax noprefix
.text
.global probe, probe_end
.hidden probe, probe_end
probe:
    mov eax, 0
    vpbroadcastq zmm0, rax
    vpaddq zmm1, zmm0, [rdi]
    vpaddq zmm17, zmm0, [rdi+64]
    mov eax, 0x1f8
    vpbroadcastb zmm3, eax
    vpsubb zmm4, zmm1, zmm3
    vpandq zmm5, zmm17, zmm3
    vpunpcklbw zmm18, zmm4, zmm5
    vpunpckhbw zmm19, zmm4, zmm5
    vshufi64x2 zmm2, zmm18, zmm19, 0x1b
    vmovdqu64 [rdi+128], zmm2
    vpaddq zmm20, zmm17, [rdi+128]
    vpsllq zmm6, zmm20, 5
    vpsrlq zmm7, zmm6, 3
    vpaddq zmm8, zmm20, zmm7
    vmovdqu64 [rdi+192], zmm8
    vzeroupper
    vmovdqu64 [rdi+256], zmm2
    vmovdqu64 [rdi+320], zmm20
    ret
probe_end:
.section .note.GNU-stack,"",@progbits
