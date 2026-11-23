From Coq Require Import List ZArith Bool Lia.
From ProofArithmetic Require Import Ranges.
From Machine Require Import execution.Blocks execution.WordBounds execution.Lane.
From Curve25519 Require Import Radix51.
From Ed25519Simd Require Import FieldTraceBounds PointFrame.
From Ed25519Simd.Point Require Import Double DoublePath Add AddPath.
Import ListNotations. Local Open Scope Z_scope.

Definition any_words : bstate := (fun _=>Range 0 (2^64-1),fun _=>Range 0 (2^64-1)).
Definition folded_rows p es j :=
  let b := beffects p j es any_words in
  forallb (fun i => includes (snd b (point,64*Z.of_nat i)) 0 folded_column_bound) (seq 0 10).
Definition check_bounds p es j := bcheck p j es any_words && folded_rows p es j.
Lemma double_bounds_checked j : check_bounds Double.program (double_effects true) j=true.
Proof. vm_compute; reflexivity. Qed.
Lemma add_bounds_checked j : check_bounds Add.program (add_effects PrivateAffine) j=true.
Proof. vm_compute; reflexivity. Qed.

Theorem folded_rows_sound p es j s : lane_words s -> check_bounds p es j=true ->
  forall i,(i<10)%nat -> 0<=cells (lane_effects p j es s) (point,64*Z.of_nat i)<=folded_column_bound.
Proof.
  intros [R M] H i I. apply Bool.andb_true_iff in H as [Check Rows].
  unfold folded_rows in Rows. rewrite forallb_forall in Rows.
  specialize (Rows i ltac:(apply in_seq;lia)). apply (includes_sound _ _ _ _ Rows).
  assert (Init : bmodels any_words s).
  { split; intro k; unfold bounded,any_words; cbn [fst snd lower_bound upper_bound];
    (specialize (R k) || specialize (M k)); unfold word64 in *; lia. }
  apply (proj2 (beffects_sound p j es any_words s Check Init)).
Qed.
