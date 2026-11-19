From Coq Require Import ZArith List Bool Lia.
From Machine Require Import Instructions.
Require Import FieldSpec Polynomial Interval.
Import ListNotations.
Open Scope Z_scope.

Definition rhs dst op := match op with
 | Copy a => V a | Load _ _ | Xor _ _ => C 0
 | Add a b => Rem (Plus (V a) (V b)) word
 | Sub a b => Rem (Plus (V a) (Times (C (-1)) (V b))) word
 | Mul a b => Rem (Times (V a) (V b)) word
 | Shl a n => Rem (Times (V a) (C (2^Z.of_nat n))) word
 | Shr a n => Quot (V a) (2^Z.of_nat n)
 | And a _ => Rem (V a) radix
 | Madd high a b => let p:=Times (Rem (V a) split) (Rem (V b) split) in
   Rem (Plus (V dst) (if high then Quot p split else Rem p split)) word end.
Definition supported op := match op with
 | Xor a b => Nat.eqb a b | And _ b => Nat.eqb b 29 | _ => true end.
Definition aexec (loads:nat -> Z -> interval) s dst op := match op with
 | Load b d => loads b d | _ => abstract s (rhs dst op) end.
Fixpoint arun hints loads code s := match code with
 | [] => s | (d,op)::tail => arun hints loads tail (put s d (refine hints (aexec loads s d op))) end.
Definition legal_instruction (i:instruction) :=
 let '(d,op):=i in encodable i && negb (Nat.eqb d 29) && supported op && legal (rhs d op).

Lemma rhs_ok load r dst op : r 29%nat=radix-1 -> supported op=true ->
 bits load r dst op = match op with Load b d => load b d | _ => val r (rhs dst op) end.
Proof.
 intros Mask Form. destruct op; cbn [supported] in Form;
 try (apply Nat.eqb_eq in Form; subst).
 all: cbv beta iota zeta delta [bits rhs val Move.copy Logic.vpxorq Logic.vpandq
   Arithmetic.vpaddq Arithmetic.vpsubq Arithmetic.vpmullq Shift.vpsllq Shift.vpsrlq IFMA.madd52 X86.low64];
 try rewrite Z.lxor_nilpotent;
 try rewrite Z.shiftl_mul_pow2 by lia;
 try rewrite Z.shiftr_div_pow2 by lia;
 repeat rewrite Z.land_ones by lia; try reflexivity.
 - rewrite Mask. change (Z.land (r a) (Z.ones 51)=r a mod (2^51)). apply Z.land_ones; lia.
 - destruct high; repeat rewrite Z.land_ones by lia;
   try rewrite Z.shiftr_div_pow2 by lia; reflexivity.
Qed.

Definition loads_of (code:list instruction) :=
 flat_map (fun i=>match snd i with Load b d=>[(b,d)] | _=>[] end) code.
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
   rewrite rhs_ok by assumption. destruct op; cbn [aexec];
   try (apply abstract_ok; assumption). apply Mem. now left.
Qed.
