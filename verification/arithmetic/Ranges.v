From Coq Require Import ZArith List Bool Lia Ring.
From ProofArithmetic Require Export Expressions.
Import ListNotations.
Open Scope Z_scope.

(* Bounds contain no expression and make no claim about an exact value. *)
Record bounds := Range { lower_bound : Z; upper_bound : Z }.
Definition bounded a z := lower_bound a<=z<=upper_bound a.
Definition min4 a b c d := Z.min (Z.min a b) (Z.min c d).
Definition max4 a b c d := Z.max (Z.max a b) (Z.max c d).
Definition add_bounds a b := Range (lower_bound a+lower_bound b) (upper_bound a+upper_bound b).
Definition multiply_bounds a b :=
 Range (min4 (lower_bound a*lower_bound b) (lower_bound a*upper_bound b)
             (upper_bound a*lower_bound b) (upper_bound a*upper_bound b))
       (max4 (lower_bound a*lower_bound b) (lower_bound a*upper_bound b)
             (upper_bound a*lower_bound b) (upper_bound a*upper_bound b)).
Definition quotient_bounds a d := Range (lower_bound a/d) (upper_bound a/d).
Definition within_modulus a d := (0<=?lower_bound a)&&(upper_bound a<?d).
Definition remainder_bounds a d := if within_modulus a d then a else Range 0 (d-1).
Fixpoint range_eval (s:nat->bounds) e := match e with
 | V i=>s i | C n=>Range n n
 | Plus a b=>add_bounds(range_eval s a)(range_eval s b)
 | Times a b=>multiply_bounds(range_eval s a)(range_eval s b)
 | Quot a d=>quotient_bounds(range_eval s a)d
 | Rem a d=>remainder_bounds(range_eval s a)d end.

Lemma product_bounds l u v w x y : l<=x<=u -> v<=y<=w ->
 min4 (l*v) (l*w) (u*v) (u*w) <= x*y <= max4 (l*v) (l*w) (u*v) (u*w).
Proof.
 intros X Y. unfold min4,max4.
 pose proof (Z.le_min_l (l*v) (l*w)). pose proof (Z.le_min_r (l*v) (l*w)).
 pose proof (Z.le_min_l (u*v) (u*w)). pose proof (Z.le_min_r (u*v) (u*w)).
 pose proof (Z.le_min_l (Z.min (l*v) (l*w)) (Z.min (u*v) (u*w))).
 pose proof (Z.le_min_r (Z.min (l*v) (l*w)) (Z.min (u*v) (u*w))).
 pose proof (Z.le_max_l (l*v) (l*w)). pose proof (Z.le_max_r (l*v) (l*w)).
 pose proof (Z.le_max_l (u*v) (u*w)). pose proof (Z.le_max_r (u*v) (u*w)).
 pose proof (Z.le_max_l (Z.max (l*v) (l*w)) (Z.max (u*v) (u*w))).
 pose proof (Z.le_max_r (Z.max (l*v) (l*w)) (Z.max (u*v) (u*w))).
 split; destruct (Z_le_dec 0 y); [destruct (Z_le_dec 0 l)|destruct (Z_le_dec 0 u)|destruct (Z_le_dec 0 u)|destruct (Z_le_dec 0 l)]; nia.
Qed.

Theorem range_eval_sound s r e : (forall i,bounded(s i)(r i)) ->legal e=true ->
 bounded(range_eval s e)(val r e).
Proof.
 intros S;induction e;cbn [legal range_eval val];intro H;
 try apply andb_true_iff in H as[H1 H2];
 unfold bounded in *;cbn [add_bounds multiply_bounds quotient_bounds lower_bound upper_bound] in *.
 - lia.
 - apply S.
 - specialize(IHe1 H1);specialize(IHe2 H2);lia.
 - apply product_bounds;auto.
 - specialize(IHe H1);apply Z.ltb_lt in H2;split;apply Z.div_le_mono;lia.
 - specialize(IHe H1);apply Z.ltb_lt in H2;unfold remainder_bounds,within_modulus.
   destruct((0<=?lower_bound(range_eval s e))&&(upper_bound(range_eval s e)<?d))eqn:B.
   + apply andb_true_iff in B as[A B];apply Z.leb_le in A;apply Z.ltb_lt in B.
     rewrite Z.mod_small by lia;exact IHe.
   + cbn [lower_bound upper_bound];pose proof(Z.mod_pos_bound(val r e)d H2);lia.
Qed.
