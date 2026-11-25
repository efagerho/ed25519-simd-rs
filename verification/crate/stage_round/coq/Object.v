From Coq Require Import Lia.
From Ed25519Simd.StageRound Require Import Program ObjectBytes Audit Routing Execution.

Theorem assembled_stage_round_correct : stage_contract symbol_bytes.
Proof.
 constructor.
 - vm_compute;split;reflexivity.
 - split;[reflexivity|intros [];reflexivity].
 - intros k c C;destruct (routed k c 0 C ltac:(lia)) as [v [_ [_ [S _]]]];now exists v.
 - intros pc s P;exact (stage_writes P).
 - exact stage_words.
 - intros pc s P [_ [_ B]];exact (stage_returns P B).
Qed.
