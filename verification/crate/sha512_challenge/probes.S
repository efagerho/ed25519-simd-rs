.intel_syntax noprefix
.text
.global sha512_round_probe
sha512_round_probe:
    vmovdqu64 zmm0, [rdi]
    vmovdqu64 zmm1, [rdi + 64]
    vmovdqu64 zmm2, [rdi + 128]
    vprorq zmm3, zmm0, 39
    vpternlogq zmm0, zmm1, zmm2, 0x96
    vpternlogq zmm1, zmm2, zmm3, 0xca
    vpternlogq zmm2, zmm3, zmm0, 0xe8
    vmovdqu64 [rdi], zmm0
    vmovdqu64 [rdi + 64], zmm1
    vmovdqu64 [rdi + 128], zmm2
    vmovdqu64 [rdi + 192], zmm3
    vzeroupper
    ret
.global sha512_shuffle_probe
sha512_shuffle_probe:
    vmovdqu64 zmm0, [rdi]
    vmovdqu64 zmm1, [rsi]
    vpshufb zmm2, zmm0, zmm1
    vmovdqu64 [rdi], zmm2
    vzeroupper
    ret
.section .note.GNU-stack,"",@progbits
