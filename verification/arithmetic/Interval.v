From Coq Require Import ZArith List Bool Lia Ring.
From ProofArithmetic Require Export Expressions.
Import ListNotations.
Open Scope Z_scope.

(* Signed mathematical intervals are needed before a wrapping subtraction.
   A remainder is removed only when BOTH ends lie in its canonical range. *)
Record interval := I { term : expr; lower : Z; upper : Z }.
Definition models env a z := val env (term a) = z /\ lower a <= z <= upper a.
Definition min4 a b c d := Z.min (Z.min a b) (Z.min c d).
Definition max4 a b c d := Z.max (Z.max a b) (Z.max c d).
Fixpoint abstract (s:nat -> interval) (e:expr) : interval :=
 match e with
 | V i => s i | C c => I (C c) c c
 | Plus a b => let x:=abstract s a in let y:=abstract s b in
   I (Plus (term x) (term y)) (lower x+lower y) (upper x+upper y)
 | Times a b => let x:=abstract s a in let y:=abstract s b in
   I (Times (term x) (term y))
     (min4 (lower x*lower y) (lower x*upper y) (upper x*lower y) (upper x*upper y))
     (max4 (lower x*lower y) (lower x*upper y) (upper x*lower y) (upper x*upper y))
 | Quot a d => let x:=abstract s a in I (Quot (term x) d) (lower x/d) (upper x/d)
 | Rem a d => let x:=abstract s a in
   if (0 <=? lower x) && (upper x <? d) then x else I (Rem (term x) d) 0 (d-1)
 end.
Fixpoint legal e := match e with
 | V _ | C _ => true
 | Plus a b | Times a b => legal a && legal b
 | Rem a d | Quot a d => legal a && (0 <? d) end.

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

Definition bounded a z := lower a<=z<=upper a.
Lemma abstract_bounds s r e : (forall i,bounded(s i)(r i)) ->legal e=true ->
 bounded(abstract s e)(val r e).
Proof.
 intros S;induction e;cbn [legal abstract val];intro H;
 try apply andb_true_iff in H as[H1 H2];
 unfold bounded in *;cbn [lower upper] in *.
 - lia.
 - apply S.
 - specialize(IHe1 H1);specialize(IHe2 H2);lia.
 - apply product_bounds;auto.
 - specialize(IHe H1);apply Z.ltb_lt in H2;split;apply Z.div_le_mono;lia.
 - specialize(IHe H1);apply Z.ltb_lt in H2.
   destruct((0<=?lower(abstract s e))&&(upper(abstract s e)<?d))eqn:B.
   + apply andb_true_iff in B as[A B];apply Z.leb_le in A;apply Z.ltb_lt in B.
     rewrite Z.mod_small by lia;exact IHe.
   + cbn [lower upper];pose proof(Z.mod_pos_bound(val r e)d H2);lia.
Qed.

Theorem abstract_ok env s r e :
 (forall i, models env (s i) (r i)) -> legal e = true ->
 models env (abstract s e) (val r e).
Proof.
 intros S H; split.
 - revert H; induction e; cbn [legal abstract val]; intro H;
   try apply andb_true_iff in H as [H1 H2].
   + reflexivity.
   + exact(proj1(S i)).
   + cbn [term val];now rewrite (IHe1 H1),(IHe2 H2).
   + cbn [term val];now rewrite (IHe1 H1),(IHe2 H2).
   + cbn [term val];now rewrite (IHe H1).
   + destruct((0<=?lower(abstract s e))&&(upper(abstract s e)<?d))eqn:B.
     * rewrite (IHe H1);symmetry;apply Z.mod_small.
       pose proof(abstract_bounds s r e (fun i=>proj2(S i)) H1)as Bounds.
       apply andb_true_iff in B as[L U];apply Z.leb_le in L;apply Z.ltb_lt in U.
       unfold bounded in Bounds;lia.
     * cbn [term val];now rewrite (IHe H1).
 - apply abstract_bounds;[intro i;exact(proj2(S i))|exact H].
Qed.

(* A caller can supply proved relational bounds, e.g. limb1+limb0/radix.
   Only exact expression equality can apply a hint; it is never assumed. *)
Definition valid_hint env h := lower h <= val env (term h) <= upper h.
Fixpoint refine hints a := match hints with
 | [] => a | h::tail => if expr_dec (term a) (term h) then h else refine tail a end.
Lemma refine_ok env hints a z :
 Forall (valid_hint env) hints -> models env a z -> models env (refine hints a) z.
Proof.
 intros H; induction H as [|h tail Hh Htail IH]; cbn [refine]; intros [E B]; [split; assumption|].
 destruct (expr_dec (term a) (term h)) as [Same|Different]; [|apply IH; split; assumption].
 unfold models,valid_hint in *. rewrite Same in E. split; [exact E|now rewrite <-E].
Qed.
Example underflow_is_wrapped :
 term (abstract (fun _=>I (C 0) 0 0) (Rem (C (-1)) (2^64))) = Rem (C (-1)) (2^64).
Proof. vm_compute; reflexivity. Qed.
Example safe_subtraction_is_exact :
 term (abstract (fun i=>if Nat.eqb i 0 then I (V 0) 100 200 else I (V 1) 0 99)
   (Rem (Plus (V 0) (Times (C (-1)) (V 1))) (2^64))) = Plus (V 0) (Times (C (-1)) (V 1)).
Proof. vm_compute; reflexivity. Qed.
