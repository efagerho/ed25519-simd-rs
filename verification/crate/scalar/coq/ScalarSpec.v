From Coq Require Import List ZArith Lia.
Import ListNotations. Open Scope Z_scope.

(* Independent public specification: all 512 input bits, canonical modulo L. *)
Definition L : Z := 2^252 + 27742317777372353535851937790883648493.
Definition B : Z := 2^52.
Definition W : Z := 2^64.
Definition R : Z := B^5.
Fixpoint number (base:Z) (xs:list Z) : Z :=
 match xs with []=>0 | x::tail=>x+base*number base tail end.
(* The buffers are row-major: row i contains word/limb i of all eight lanes. *)
Definition lane_input (words : nat -> Z) j :=
  number W (map (fun i => words (8*i+j)%nat) (seq 0 8)).
Definition lane_output (words : nat -> Z) j :=
  number B (map (fun i => words (8*i+j)%nat) (seq 0 5)).

Definition scalar_spec (before after : nat -> Z) :=
  forall j, (j < 8)%nat ->
    lane_output after j = lane_input before j mod L /\
    (forall i, (i < 5)%nat -> 0 <= after (8*i+j)%nat < B).

Lemma L_positive : 0<L. Proof. unfold L;lia. Qed.
Lemma B_positive : 0<B. Proof. unfold B;lia. Qed.
Lemma W_positive : 0<W. Proof. unfold W;lia. Qed.
Lemma number_bound base xs : 0<base ->Forall(fun x=>0<=x<base)xs ->
 0<=number base xs<base^Z.of_nat(length xs).
Proof.
 intros Base Bounds;induction Bounds;cbn [number length];[cbn;lia|].
 rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia;nia.
Qed.
