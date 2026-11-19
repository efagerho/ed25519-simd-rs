From ProofArithmetic Require Import Interval.
From Coq Require Import ZArith List Bool Lia.
From Machine Require Import Instructions.
Require Import FieldSpec Polynomial.
From ProofArithmetic Require Symbolic.
Import ListNotations.
Open Scope Z_scope.

Definition rhs := ProofArithmetic.Symbolic.rhs 51.
Definition madd_expr := ProofArithmetic.Symbolic.madd_expr.
Definition legal_rhs dst op := match rhs dst op with
 | Some e => legal e | None => match op with Load _ _ | MaddMem _ _ _ _ => true | _ => false end end.
Definition supported op := match op with
 | Xor a b => Nat.eqb a b | And _ b => Nat.eqb b 29 | _ => true end.
Definition madd_inputs {A} (acc lhs rhs:A) i :=
 if Nat.eqb i 0 then acc else if Nat.eqb i 1 then lhs else rhs.
Definition aexec (loads:nat -> Z -> interval) s dst op := match op with
 | MaddMem high a b d => abstract (madd_inputs (s dst) (s a) (loads b d)) (madd_expr high (V 0) (V 1) (V 2))
 | Load b d => loads b d
 | _ => match rhs dst op with Some e => abstract s e | None => s dst end end.
Fixpoint arun hints loads code s := match code with
 | [] => s | (d,op)::tail => arun hints loads tail (put s d (refine hints (aexec loads s d op))) end.
Definition legal_instruction (i:instruction) :=
 let '(d,op):=i in encodable i && negb (Nat.eqb d 29) && supported op && legal_rhs d op.

Lemma rhs_ok load r dst op e : r 29%nat=radix-1 -> supported op=true ->
 rhs dst op=Some e -> bits load r dst op=val r e.
Proof.
 intros Mask Form;apply ProofArithmetic.Symbolic.rhs_ok;[lia|].
 destruct op;cbn [supported] in Form;cbn [ProofArithmetic.Symbolic.operand_ok];
 try exact Logic.I;try(now apply Nat.eqb_eq in Form).
 apply Nat.eqb_eq in Form;subst b;rewrite Mask;reflexivity.
Qed.

Lemma madd_value high acc lhs rhs0 :
 IFMA.madd52 high acc lhs rhs0 = val (madd_inputs acc lhs rhs0) (madd_expr high (V 0) (V 1) (V 2)).
Proof.
 unfold IFMA.madd52, X86.low64;cbn [madd_expr ProofArithmetic.Symbolic.madd_expr val madd_inputs Nat.eqb].
 repeat rewrite Z.land_ones by lia;destruct high;
 try rewrite Z.shiftr_div_pow2 by lia;reflexivity.
Qed.

Definition loads_of (code:list instruction) :=
 flat_map (fun i=>match snd i with Load b d | MaddMem _ _ b d=>[(b,d)] | _=>[] end) code.
Theorem run_ok env hints loads load code s r :
 Forall (valid_hint env) hints ->
 (forall b d, In (b,d) (loads_of code) -> models env (loads b d) (load b d)) ->
 r 29%nat=radix-1 -> (forall i, models env (s i) (r i)) ->
 forallb legal_instruction code=true ->
 forall j, models env (arun hints loads code s j) (run load code r j).
Proof.
 intro Hints; revert s r; induction code as [|[d op] tail IH]; intros s r Mem Mask R Check;
 cbn [arun run]; [exact R|].
 apply andb_true_iff in Check as [Head Tail]. unfold legal_instruction in Head.
 repeat rewrite andb_true_iff in Head. destruct Head as [[[Encode Dest] Form] Legal].
 apply negb_true_iff in Dest. apply IH; auto.
 - intros b disp Member. apply Mem. unfold loads_of in *; cbn [flat_map snd].
   apply in_or_app; now right.
 - unfold put; rewrite Dest; exact Mask.
 - intro j; unfold put; destruct (Nat.eqb d j); [|apply R].
   apply refine_ok; [exact Hints|].
   destruct op; cbn [aexec rhs ProofArithmetic.Symbolic.rhs legal_rhs] in *;
   try (erewrite rhs_ok by (eassumption || reflexivity); apply abstract_ok; assumption).
   + apply Mem;now left.
   + change (models env
       (abstract (madd_inputs (s d) (s a) (loads base disp)) (madd_expr high (V 0) (V 1) (V 2)))
       (IFMA.madd52 high (r d) (r a) (load base disp))).
   rewrite madd_value. apply (abstract_ok env _ (madd_inputs (r d) (r a) (load base disp))).
     * intro i;unfold madd_inputs;destruct (Nat.eqb i 0),(Nat.eqb i 1);auto.
     apply Mem;now left.
     * destruct high;reflexivity.
Qed.
