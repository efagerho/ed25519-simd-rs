From Coq Require Import List ZArith Lia Ring.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
Import ListNotations. Open Scope Z_scope.

Definition exponent := (prime-5)/8.
Definition public_bound i := if Nat.eqb i 1 then radix+511 else radix-1.
Definition pow2_spec (a b out:nat -> Z) :=
 (forall i j, (i<5)%nat -> (j<8)%nat ->
  0<=cell a i j<split /\ 0<=cell b i j<split) ->
 forall (second:bool) j, (j<8)%nat ->
 let start:=if second then 5%nat else 0%nat in
 (forall i, (i<5)%nat -> 0<=cell out (start+i)%nat j<=public_bound i) /\
 field_at out start j mod prime =
 ((field_at (if second then b else a) 0%nat j)^exponent) mod prime.
