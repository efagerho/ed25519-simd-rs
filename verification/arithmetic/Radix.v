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

(* Add one most-significant digit to two bounded low parts. *)
Lemma compare_digit place a b x y :
 0 <= a < place -> 0 <= b < place ->
 (a+place*x <? b+place*y) = (((a <? b) && (x =? y)) || (x <? y))%bool.
Proof.
 intros A B. apply Bool.eq_true_iff_eq.
 rewrite Bool.orb_true_iff, Bool.andb_true_iff, !Z.ltb_lt, Z.eqb_eq.
 destruct (Z.compare_spec x y); subst; intuition nia.
Qed.

Fixpoint low_digits base (xs:nat -> Z) n :=
 match n with O => 0 | S i => low_digits base xs i + base^Z.of_nat i * xs i end.

Lemma subtraction_chain base (xs ys digits borrow:nat -> Z) n :
 borrow 0%nat = 0 ->
 (forall i, (i<n)%nat -> 0 <= borrow i <= 1 ->
    0 <= borrow (S i) <= 1 /\
    xs i - ys i - borrow i = digits i - base*borrow (S i)) ->
 0 <= borrow n <= 1 /\ low_digits base xs n-low_digits base ys n =
 low_digits base digits n - base^Z.of_nat n * borrow n.
Proof.
 intros Zero Step. induction n as [|i IH].
 - rewrite Zero; cbn; lia.
 - destruct (IH ltac:(intros; apply Step; [lia|assumption])) as [B Prev].
   destruct (Step i ltac:(lia) B) as [Next D]. split; [exact Next|].
   cbn [low_digits]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
   nia.
Qed.

Lemma conditional_subtraction modulus capacity x difference borrow :
 0 < modulus -> 0 <= x < 2*modulus -> 0 <= difference < capacity ->
 0 <= borrow <= 1 -> x-modulus = difference-capacity*borrow ->
 (if borrow =? 0 then difference else x) = x mod modulus.
Proof.
 intros M X D B E. destruct (Z.eqb_spec borrow 0) as [->|N].
 - replace difference with (x-modulus) by lia.
   apply Z.mod_unique with (q:=1); [left; lia|ring].
 - assert (borrow=1) as -> by lia. symmetry; apply Z.mod_small; lia.
Qed.
