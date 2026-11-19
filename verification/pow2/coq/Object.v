From Coq Require Import ZArith List.
From Machine Require Import Blocks.
Require Import Program Pow2ABI Pow2Memory Pow2Bytes FieldSpec.
Require Audit Execution FrameProof ObjectBytes.

Definition object_bytes := ObjectBytes.symbol_bytes.

Local Lemma logical_execution size initial a b : valid_pow2_entry initial a b ->
 exists final, returns pow2_program abi_layout initial final /\
   stack_restored initial final /\ registers_preserved initial final /\
   memory_safe pow2_program size initial final /\ pow2_spec a b (output_words initial final).
Proof.
 intro Entry.
 destruct (Execution.pow2_returns_correct initial a b Entry) as [final [R [SP Field]]].
 destruct (FrameProof.pow2_frame_correct size initial a b final Entry R) as [Regs Mem].
 exists final. split; [exact R|]. split; [exact SP|].
 split; [exact Regs|]. split; assumption.
Qed.

(** This theorem proves the contract explained in [Audit.pow2_contract] for
    the bytes extracted from the linked function being checked. *)
Theorem assembled_symbol_correct : Audit.pow2_contract object_bytes.
Proof.
  split.
  - vm_compute. reflexivity.
  - split.
    + exact Execution.block_layout_checked.
    + split; [apply logical_execution|].
      apply concrete_contract_from_logical, logical_execution.
Qed.

Print Assumptions assembled_symbol_correct.
