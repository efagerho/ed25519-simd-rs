From Coq Require Import List ZArith Lia.
From Curve25519 Require Export ScalarReduction.
From ProofArithmetic Require Export Radix.
Import ListNotations. Open Scope Z_scope.

(* The buffers are row-major: row i contains word/limb i of all eight lanes. *)
Definition lane_input (words : nat -> Z) j :=
  number W (map (fun i => words (8*i+j)%nat) (seq 0 8)).
Definition lane_output (words : nat -> Z) j :=
  number B (map (fun i => words (8*i+j)%nat) (seq 0 5)).

Definition scalar_spec (before after : nat -> Z) :=
  forall j, (j < 8)%nat ->
    lane_output after j = lane_input before j mod L /\
    (forall i, (i < 5)%nat -> 0 <= after (8*i+j)%nat < B).
