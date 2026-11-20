.intel_syntax noprefix
.text
.global probe, probe_end
.hidden probe, probe_end
probe:
    vpbroadcastq zmm30, qword ptr [rip + .Lconstant]
    vpaddq zmm18, zmm30, [rdi]
    vpsubq zmm19, zmm30, [rsi]
    vpcmpeqq k5, zmm18, zmm19
    kmovw eax, k5
    cmp eax, 255
    # Request the near form even though the alternate return fits a short jump.
    {disp32} je .Lreturn
    vmovdqu64 zmm29, [rsi + 64]
    vpcmpeqq k3, zmm18, zmm29
    vpcmpeqq k4, zmm19, zmm29
    korw k3, k4, k3
    kmovw eax, k3
.Lreturn:
    ret
.Lconstant:
    .quad 0x0123456789abcdef
probe_end:
.section .note.GNU-stack,"",@progbits
