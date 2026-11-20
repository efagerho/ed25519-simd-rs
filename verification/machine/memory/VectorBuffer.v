From Coq Require Import ZArith Lia.
From Machine Require Import execution.MachineState.
Open Scope Z_scope.

(* One 512-bit memory cell holds eight consecutive qwords. *)
Definition vector_address (region : nat) (base : Z) (i : nat) : pointer :=
 (region, base + 64 * Z.of_nat i).
Definition words_at (m : pointer -> vector) region k :=
 m (vector_address region 0 (k / 8)) (k mod 8)%nat.

Lemma words_at_lane m region i j : (j < 8)%nat ->
 words_at m region (i * 8 + j)%nat = m (vector_address region 0 i) j.
Proof.
 intros J; unfold words_at.
 assert (D : ((i*8+j)/8=i)%nat) by (symmetry; apply Nat.div_unique with (r:=j); lia).
 assert (R : ((i*8+j) mod 8=j)%nat) by (symmetry; apply Nat.mod_unique with (q:=i); lia).
 now rewrite D,R.
Qed.
