.intel_syntax noprefix
.text
.global probe, probe_end
.hidden probe, probe_end
probe:
    vmovdqu64 zmm0, [rdi]
    vpcmpuq k1, zmm0, qword ptr [rip+.Lthreshold]{1to8}, 1
    korw k3, k1, k1
    vpcmpeqq k2, zmm0, qword ptr [rip+.Lthreshold]{1to8}
    korw k1, k1, k2
    vpcmpeqq k2{k1}, zmm0, zmm0
    vpcmpuq k4, zmm0, qword ptr [rip+.Lthreshold]{1to8}, 5
    mov eax, 1
    vpbroadcastq zmm1, rax
    vpaddq zmm0{k3}, zmm0, zmm1
    vpblendmq zmm4{k2}, zmm1, zmm0
    vpcmpuq k2{k4}, zmm0, qword ptr [rip+.Lthreshold]{1to8}, 5
    vmovdqu64 [rdi], zmm4
    kmovw eax, k2
    ret
.Lthreshold:
    .quad 0x8000000000000000
probe_end:
.section .note.GNU-stack,"",@progbits
