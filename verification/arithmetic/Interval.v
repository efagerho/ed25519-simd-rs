From Coq Require Import ZArith List Bool Lia Ring.
From ProofArithmetic Require Export Ranges.
Import ListNotations.
Open Scope Z_scope.

(* Exact symbolic values carry a separate numeric enclosure. I is the
   convenient constructor for expressions with two explicit endpoints. *)
Record interval := SymbolicValue { term : expr; enclosure : bounds }.
Definition I e lo hi := SymbolicValue e (Range lo hi).
Definition lower a := lower_bound(enclosure a).
Definition upper a := upper_bound(enclosure a).
Definition models env a z := val env(term a)=z /\ lower a<=z<=upper a.
Fixpoint abstract (s:nat->interval) e : interval := match e with
 | V i=>s i | C n=>I(C n)n n
 | Plus a b=>let x:=abstract s a in let y:=abstract s b in
   SymbolicValue(Plus(term x)(term y))(add_bounds(enclosure x)(enclosure y))
 | Times a b=>let x:=abstract s a in let y:=abstract s b in
   SymbolicValue(Times(term x)(term y))(multiply_bounds(enclosure x)(enclosure y))
 | Quot a d=>let x:=abstract s a in
   SymbolicValue(Quot(term x)d)(quotient_bounds(enclosure x)d)
 | Rem a d=>let x:=abstract s a in
   if within_modulus(enclosure x)d then x else SymbolicValue(Rem(term x)d)(Range 0(d-1)) end.
Lemma abstract_enclosure s e : enclosure(abstract s e)=range_eval(fun i=>enclosure(s i))e.
Proof.
 induction e;cbn [abstract range_eval I enclosure];try reflexivity;
 try now rewrite ?IHe1,?IHe2,?IHe.
 unfold remainder_bounds;rewrite <-IHe;destruct(within_modulus(enclosure(abstract s e))d);reflexivity.
Qed.
Lemma abstract_bounds s r e : (forall i,bounded(enclosure(s i))(r i)) ->legal e=true ->
 bounded(enclosure(abstract s e))(val r e).
Proof. rewrite abstract_enclosure;apply range_eval_sound. Qed.

Theorem abstract_ok env s r e :
 (forall i,models env(s i)(r i)) ->legal e=true ->models env(abstract s e)(val r e).
Proof.
 intros S H;split.
 - revert H;induction e;cbn [legal abstract val];intro H;
   try apply andb_true_iff in H as[H1 H2].
   + reflexivity.
   + exact(proj1(S i)).
   + cbn [term val];now rewrite (IHe1 H1),(IHe2 H2).
   + cbn [term val];now rewrite (IHe1 H1),(IHe2 H2).
   + cbn [term val];now rewrite (IHe H1).
   + destruct(within_modulus(enclosure(abstract s e))d)eqn:B.
     * rewrite(IHe H1);symmetry;apply Z.mod_small.
       pose proof(abstract_bounds s r e (fun i=>proj2(S i)) H1)as Bound.
       unfold within_modulus in B;apply andb_true_iff in B as[L U];
       apply Z.leb_le in L;apply Z.ltb_lt in U;unfold bounded in Bound;lia.
     * cbn [term val];now rewrite(IHe H1).
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
