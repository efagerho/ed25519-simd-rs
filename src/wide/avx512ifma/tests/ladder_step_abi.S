// Native ABI probe: seed every SysV callee-saved GPR, call the real symbol,
// check the registers and caller stack, then restore the Rust caller's state.
// R10 supplies an additional 0/16/32/48-byte stack offset.
.text
.macro check_ladder_abi callee
    push rbp
    push rbx
    push r12
    push r13
    push r14
    push r15
    sub rsp, 24
    sub rsp, r10
    mov [rsp + 16], r10
    mov [rsp], rsp
    mov rax, 0x123456789abcdef0
    mov [rsp + 8], rax
    mov rbp, rax
    lea rbx, [rax + 1]
    lea r12, [rax + 2]
    lea r13, [rax + 3]
    lea r14, [rax + 4]
    lea r15, [rax + 5]
    call \callee
    mov rdx, 0x123456789abcdef0
    mov eax, 1
    cmp rbp, rdx
    jne 1f
    inc eax
    inc rdx
    cmp rbx, rdx
    jne 1f
    inc eax
    inc rdx
    cmp r12, rdx
    jne 1f
    inc eax
    inc rdx
    cmp r13, rdx
    jne 1f
    inc eax
    inc rdx
    cmp r14, rdx
    jne 1f
    inc eax
    inc rdx
    cmp r15, rdx
    jne 1f
    inc eax
    cmp [rsp], rsp
    jne 1f
    inc eax
    mov rdx, 0x123456789abcdef0
    cmp [rsp + 8], rdx
    jne 1f
    xor eax, eax
1:
    add rsp, [rsp + 16]
    add rsp, 24
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    pop rbp
    ret
.endm

.globl ed25519_simd_test_ladder_step_abi
.hidden ed25519_simd_test_ladder_step_abi
.type ed25519_simd_test_ladder_step_abi,@function
ed25519_simd_test_ladder_step_abi:
    mov r10, rcx
    check_ladder_abi ed25519_simd_ladder_step_ifma
.size ed25519_simd_test_ladder_step_abi, .-ed25519_simd_test_ladder_step_abi

.globl ed25519_simd_test_mul_public_abi
.hidden ed25519_simd_test_mul_public_abi
.type ed25519_simd_test_mul_public_abi,@function
ed25519_simd_test_mul_public_abi:
    mov r10, [rsp + 8]          // seventh argument, after the return address
    check_ladder_abi ed25519_simd_mul_s_base_minus_k_public
.size ed25519_simd_test_mul_public_abi, .-ed25519_simd_test_mul_public_abi
.purgem check_ladder_abi
