// Native ABI probe: seed every SysV callee-saved GPR, call the real symbol,
// check the registers and caller stack, then restore the Rust caller's state.
// R8 is an additional 0/16/32/48-byte stack offset, to exercise every
// possible SysV stack alignment modulo a 64-byte vector.
.text
.globl ed25519_simd_test_cached_add_abi
.hidden ed25519_simd_test_cached_add_abi
.type ed25519_simd_test_cached_add_abi,@function
ed25519_simd_test_cached_add_abi:
    push rbp
    push rbx
    push r12
    push r13
    push r14
    push r15
    sub rsp, 24
    sub rsp, r8
    mov [rsp + 16], r8
    mov [rsp], rsp
    mov rax, 0x123456789abcdef0
    mov [rsp + 8], rax
    mov rbp, rax
    lea rbx, [rax + 1]
    lea r12, [rax + 2]
    lea r13, [rax + 3]
    lea r14, [rax + 4]
    lea r15, [rax + 5]
    call ed25519_simd_add_cached_ifma
    mov rdx, 0x123456789abcdef0
    mov eax, 1
    cmp rbp, rdx
    jne .Lca_abi_done
    inc eax
    inc rdx
    cmp rbx, rdx
    jne .Lca_abi_done
    inc eax
    inc rdx
    cmp r12, rdx
    jne .Lca_abi_done
    inc eax
    inc rdx
    cmp r13, rdx
    jne .Lca_abi_done
    inc eax
    inc rdx
    cmp r14, rdx
    jne .Lca_abi_done
    inc eax
    inc rdx
    cmp r15, rdx
    jne .Lca_abi_done
    inc eax
    cmp [rsp], rsp
    jne .Lca_abi_done
    inc eax
    mov rdx, 0x123456789abcdef0
    cmp [rsp + 8], rdx
    jne .Lca_abi_done
    xor eax, eax
.Lca_abi_done:
    add rsp, [rsp + 16]
    add rsp, 24
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    pop rbp
    ret
.size ed25519_simd_test_cached_add_abi, .-ed25519_simd_test_cached_add_abi
