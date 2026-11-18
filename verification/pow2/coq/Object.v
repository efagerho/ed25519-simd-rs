From Coq Require Import ZArith List.
Require Audit Execution FrameProof ObjectBytes.

Definition object_bytes := ObjectBytes.symbol_bytes.

(** This theorem proves the contract explained in [Audit.pow2_contract] for
    the bytes extracted from the linked function being checked. *)
Theorem assembled_symbol_correct : Audit.pow2_contract object_bytes.
Proof.
  split.
  - vm_compute. reflexivity.
  - split.
    + exact Execution.block_layout_checked.
    + intros initial a b Entry.
      destruct (Execution.pow2_returns_correct initial a b Entry) as [final [R [SP Field]]].
      destruct (FrameProof.pow2_frame_correct (Z.of_nat (List.length object_bytes))
                initial a b final Entry R) as [Regs Mem].
      exists final. split; [exact R|]. split; [exact SP|].
      split; [exact Regs|]. split; assumption.
Qed.

Print Assumptions assembled_symbol_correct.
