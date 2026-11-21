From Coq Require Import ZArith Lia.
From Curve25519.group Require Import Affine.
Local Open Scope Z_scope.

Definition scale z P :=
 if z <? 0 then multiple (Z.to_nat (-z)) (negative P) else multiple (Z.to_nat z) P.

Lemma cancel_left P Q R : plus P Q = plus P R -> Q=R.
Proof.
 intro E;apply (f_equal (plus (negative P))) in E.
 rewrite <- !plus_assoc, (plus_comm (negative P) P), plus_negative, !plus_identity in E;exact E.
Qed.
Lemma scale_succ z P : scale (Z.succ z) P=plus P (scale z P).
Proof.
 unfold scale;destruct (z <? 0) eqn:A, (Z.succ z <? 0) eqn:B;
 apply Z.ltb_lt in A || apply Z.ltb_ge in A;
 apply Z.ltb_lt in B || apply Z.ltb_ge in B;try lia.
 - replace (Z.to_nat (-z)) with (S (Z.to_nat (- Z.succ z))) by lia.
   cbn [multiple];rewrite <-plus_assoc,plus_negative,plus_identity;reflexivity.
 - assert (z= -1) by lia;subst;change (identity=plus P (plus (negative P) identity)).
   rewrite <-plus_assoc,plus_negative,plus_identity;reflexivity.
 - replace (Z.to_nat (Z.succ z)) with (S (Z.to_nat z)) by lia;reflexivity.
Qed.
Lemma scale_add a b P : scale (a+b) P=plus (scale a P) (scale b P).
Proof.
 revert a;apply Z.bi_induction.
 - intros x y ->;reflexivity.
 - change (scale b P=plus identity (scale b P));now rewrite plus_identity.
 - intro a;replace (Z.succ a+b) with (Z.succ (a+b)) by lia.
   rewrite !scale_succ,plus_assoc;split;[intros ->;reflexivity|apply cancel_left].
Qed.
Lemma times_scale n z P : multiple n (scale z P)=scale (Z.of_nat n*z) P.
Proof.
 induction n;[reflexivity|]. cbn [multiple];rewrite IHn, Nat2Z.inj_succ.
 replace (Z.succ (Z.of_nat n)*z) with (z+Z.of_nat n*z) by ring;apply eq_sym,scale_add.
Qed.
