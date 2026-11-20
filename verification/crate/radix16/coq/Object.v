From Coq Require Import ZArith List Lia.
From Machine Require Import execution.Packed.
From Ed25519Simd.Scalar Require Object Audit ObjectBytes.
From Ed25519Simd.Radix16 Require Import LinkedBytes Routing Audit Execution.

Theorem assembled_digest_to_radix16_correct :
 digest_contract wrapper_pc symbol_bytes reducer_pc Ed25519Simd.Scalar.ObjectBytes.symbol_bytes.
Proof.
 constructor.
 - vm_compute;split;reflexivity.
 - exact (Ed25519Simd.Scalar.Audit.code_matches Ed25519Simd.Scalar.Object.assembled_scalar_correct).
 - vm_compute; intuition discriminate.
 - intros j J;destruct(routed j 0 J ltac:(lia)) as [v [Store _]];now exists v.
 - exact digest_returns.
Qed.
