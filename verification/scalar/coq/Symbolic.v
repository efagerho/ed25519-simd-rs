From ProofArithmetic Require Import Interval Polynomial.
From Coq Require Import List ZArith Bool Lia Ring.
From Machine Require Import Instructions.
Require Import ScalarSpec.
From ProofArithmetic Require Symbolic.
Import ListNotations. Open Scope Z_scope.

(* This checker reuses the existing proved interval and polynomial engines.
   Masks are checked at each instruction; no special mask register is trusted. *)
Definition rhs := ProofArithmetic.Symbolic.rhs 52.
Definition step loads s dst op := match op with
 | Load b d=>loads b d | _=>abstract s(rhs dst op) end.
Definition singleton a n := (lower a=?n)&&(upper a=?n).
Definition supported s op := match op with
 | Xor a b=>Nat.eqb a b | And _ b=>singleton(s b)(B-1)
 | MaddMem _ _ _ _=>false | _=>true end.
Definition legal_step s (i:instruction) := encodable i && supported s(snd i) && legal(rhs(fst i)(snd i)).
Fixpoint arun loads code s := match code with []=>s | (d,op)::tail=>
 arun loads tail(put s d(step loads s d op)) end.
Fixpoint check loads code s := match code with []=>true | (d,op)::tail=>
 legal_step s(d,op) && check loads tail(put s d(step loads s d op)) end.
Definition loads_of (code:list instruction) := flat_map(fun i=>match snd i with Load b d=>[(b,d)] | _=>[] end)code.
Lemma singleton_sound env (s:nat->interval) (r:nat->Z) b n : (forall i,models env(s i)(r i)) ->
 singleton(s b)n=true ->r b=n.
Proof. intros H E;unfold singleton in E;rewrite andb_true_iff,!Z.eqb_eq in E.
 destruct(H b)as[_ Bound];destruct E;lia. Qed.
Lemma rhs_ok env s load r d op : (forall i,models env(s i)(r i)) ->supported s op=true ->
 bits load r d op=match op with Load b disp=>load b disp | _=>val r(rhs d op) end.
Proof.
 intros M Form.
 pose proof(ProofArithmetic.Symbolic.rhs_ok 52 load r d op ltac:(lia))as Sound.
 destruct op;cbn [supported] in Form;try discriminate;
 apply Sound;cbn [ProofArithmetic.Symbolic.operand_ok];try exact Logic.I.
 - now apply Nat.eqb_eq in Form.
 - pose proof(singleton_sound env s r b (B-1) M Form)as Mask;rewrite Mask;reflexivity.
Qed.
Theorem run_ok env loads load code s r :
 (forall b d,In(b,d)(loads_of code)->models env(loads b d)(load b d)) ->
 (forall i,models env(s i)(r i)) ->check loads code s=true ->
 forall i,models env(arun loads code s i)(run load code r i).
Proof.
 revert s r;induction code as[|[d op]tail IH];intros s r Mem Reg Check;[exact Reg|].
 cbn [check] in Check;apply andb_true_iff in Check as[Head Tail].
 unfold legal_step in Head;cbn [fst snd] in Head.
 repeat rewrite andb_true_iff in Head;destruct Head as[[Enc Form]Legal].
 cbn [arun run];apply IH;[| |exact Tail].
 - intros b disp I;apply Mem;unfold loads_of in *;cbn;apply in_or_app;now right.
 - intro i;unfold put;destruct(Nat.eqb d i);[|apply Reg].
   rewrite(rhs_ok env s load r d op Reg Form).
   destruct op;cbn [step];try(apply abstract_ok;assumption).
   apply Mem;now left.
Qed.

Fixpoint numberE base (xs:list expr) := match xs with []=>C 0 | x::tail=>Plus x(Times(C base)(numberE base tail))end.
Lemma numberE_sound env base xs : val env(numberE base xs)=number base(map(val env)xs).
Proof. induction xs;cbn;congruence. Qed.
