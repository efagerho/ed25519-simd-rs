From Coq Require Import List ZArith Lia Ring.
Import ListNotations. Open Scope Z_scope.

Fixpoint number (base:Z) (xs:list Z) : Z :=
 match xs with []=>0 | x::tail=>x+base*number base tail end.
Lemma number_bound base xs : 0<base ->Forall(fun x=>0<=x<base)xs ->
 0<=number base xs<base^Z.of_nat(length xs).
Proof.
 intros Base Bounds;induction Bounds;cbn [number length];[cbn;lia|].
 rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia;nia.
Qed.
