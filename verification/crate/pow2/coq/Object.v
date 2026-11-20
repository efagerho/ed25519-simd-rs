From Coq Require Import ZArith List.
From Machine Require Import execution.Blocks execution.LayoutProofs execution.ScalarRefinement.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Pow2 Require Import Program Pow2ABI Pow2Memory Pow2Bytes Pow2Spec.
From Ed25519Simd.Pow2 Require Audit Execution FrameProof ObjectBytes.

Definition object_bytes := ObjectBytes.symbol_bytes.

Lemma logical_execution size initial a b : valid_pow2_entry initial a b ->
 exists final, returns pow2_program abi_layout initial final /\
   stack_restored initial final /\ registers_preserved initial final /\
   memory_safe pow2_program size initial final /\ output_initialized pow2_program initial final /\
   pow2_spec a b (output_words initial final).
Proof.
 intro Entry.
 destruct (Execution.pow2_returns_correct initial a b Entry) as [final [R [SP Field]]].
 destruct (FrameProof.pow2_frame_correct size initial a b final Entry R) as [Regs [Mem Init]].
 exists final. split; [exact R|]. split; [exact SP|].
 split; [exact Regs|]. split; [exact Mem|]. split; assumption.
Qed.

(** This theorem proves the contract explained in [Audit.pow2_contract] for
    the bytes extracted from the linked function being checked. *)
Theorem assembled_symbol_correct : Audit.pow2_contract object_bytes.
Proof.
 constructor.
 - vm_compute; reflexivity.
 - exact Execution.block_layout_checked.
 - apply concrete_contract_from_logical,logical_execution.
Qed.

Print Assumptions assembled_symbol_correct.
