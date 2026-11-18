From Coq Require Import ZArith List Bool Lia.
From Machine Require Import Instructions.
Require Import FieldSpec Polynomial Pow2Caller.
Import ListNotations.
Open Scope Z_scope.

Definition rhs dst op :=
 match op with
 | Copy a => V a | Load _ disp => V (rhs_index disp) | Xor _ _ => C 0
 | Add a b => Rem (Plus (V a) (V b)) word
 | Mul a b => Rem (Times (V a) (V b)) word
 | Shl a n => Rem (Times (V a) (C (2^Z.of_nat n))) word
 | Shr a n => Quot (V a) (2^Z.of_nat n)
 | And a _ => Rem (V a) radix
 | Madd high a b =>
   let p := Times (Rem (V a) split) (Rem (V b) split) in
   Rem (Plus (V dst) (if high then Quot p split else Rem p split)) word
 end.
Lemma bits_ok load r dst op :
 (forall disp, load 8%nat disp = r (rhs_index disp)) ->
 r 29%nat = radix-1 -> kernel_form op = true ->
 bits load r dst op = val r (rhs dst op).
Proof.
 intros Mem Mask Form. destruct op; cbn [kernel_form] in Form;
 try (apply Nat.eqb_eq in Form; subst).
 all: cbv beta iota zeta delta [bits rhs val Move.copy Logic.vpxorq Logic.vpandq
   Arithmetic.vpaddq Arithmetic.vpmullq Shift.vpsllq Shift.vpsrlq IFMA.madd52 X86.low64];
 try rewrite Z.lxor_nilpotent;
 try rewrite Z.shiftl_mul_pow2 by lia;
 try rewrite Z.shiftr_div_pow2 by lia;
 repeat rewrite Z.land_ones by lia; try reflexivity.
 - apply Mem.
 - rewrite Mask. change (Z.land (r a) (Z.ones 51) = r a mod (2^51)).
   apply Z.land_ones; lia.
 - destruct high; repeat rewrite Z.land_ones by lia;
   try rewrite Z.shiftr_div_pow2 by lia; reflexivity.
Qed.

Record absword := W { term:expr; maximum:Z }.
Fixpoint abstract (s:nat -> absword) (e:expr) : absword :=
 match e with
 | V i => s i | C c => W (C c) c
 | Plus a b => let x:=abstract s a in let y:=abstract s b in
   W (Plus (term x) (term y)) (maximum x+maximum y)
 | Times a b => let x:=abstract s a in let y:=abstract s b in
   W (Times (term x) (term y)) (maximum x*maximum y)
 | Quot a d => let x:=abstract s a in W (Quot (term x) d) (maximum x/d)
 | Rem a d => let x:=abstract s a in
   if maximum x <? d then x else W (Rem (term x) d) (d-1)
 end.
Definition models env (a:absword) z :=
 val env (term a) = z /\ 0 <= z <= maximum a.
Fixpoint legal e :=
 match e with V _ => true | C z => 0 <=? z
 | Plus a b | Times a b => legal a && legal b
 | Rem a d | Quot a d => legal a && (0 <? d) end.
Lemma abstract_ok env s r e :
 (forall i, models env (s i) (r i)) -> legal e = true ->
 models env (abstract s e) (val r e).
Proof.
 intros S; induction e; cbn [legal abstract val]; intro H;
 try apply Bool.andb_true_iff in H as [H1 H2];
 unfold models in *; cbn [term maximum val] in *.
 - apply Z.leb_le in H; lia.
 - apply S.
 - destruct (IHe1 H1), (IHe2 H2); split; [congruence | lia].
 - destruct (IHe1 H1), (IHe2 H2); split; [congruence | nia].
 - destruct (IHe H1) as [E B]. apply Z.ltb_lt in H2; rewrite E.
   split; [reflexivity|split; [apply Z.div_pos|apply Z.div_le_mono];lia].
 - destruct (IHe H1) as [E B]. apply Z.ltb_lt in H2.
   destruct (maximum (abstract s e) <? d) eqn:H.
   + apply Z.ltb_lt in H. rewrite Z.mod_small by lia. auto.
   + cbn [term maximum val]. rewrite E. pose proof (Z.mod_pos_bound (val r e) d H2); lia.
Qed.
Fixpoint arun (code:list instruction) (s:nat -> absword) :=
 match code with [] => s | (dst,op)::xs =>
 arun xs (put s dst (abstract s (rhs dst op))) end.
Definition legal_instruction (i:instruction) :=
 let '(d,op):=i in Nat.ltb d 32 && negb (Nat.eqb d 29) && kernel_form op && legal (rhs d op).
Lemma run_ok env load code s r :
 (forall disp, load 8%nat disp = r (rhs_index disp)) ->
 r 29%nat=radix-1 ->
 (forall i, models env (s i) (r i)) ->
 forallb legal_instruction code = true ->
 forall j, models env (arun code s j) (run load code r j).
Proof. revert s r; induction code as [|[d op] xs IH]; intros s r Mem Mask H G;
 cbn [arun run]; auto. apply Bool.andb_true_iff in G as [A B].
 unfold legal_instruction in A. repeat rewrite Bool.andb_true_iff in A.
 destruct A as [[[Reg D] Form] Legal]. apply Bool.negb_true_iff in D.
 apply IH.
 - intro disp. unfold put. rewrite Mem.
   assert (E : Nat.eqb d (rhs_index disp) = false).
   { apply Nat.eqb_neq. apply Nat.ltb_lt in Reg. unfold rhs_index; lia. }
   now rewrite E.
 - unfold put; rewrite D; exact Mask.
 - intro i; unfold put; destruct (Nat.eqb d i); auto.
   rewrite bits_ok by assumption. apply abstract_ok; auto.
 - exact B.
Qed.

Definition imax := split-1.
Definition smax (i:nat) := if Nat.odd (i mod 5) then imax else radix-1.
Definition omax (i:nat) := if Nat.eqb (i mod 5) 1 then radix+511 else radix-1.
Definition initial sq i :=
 if Nat.eqb i 28 then W (C 19) 19 else
 if Nat.eqb i 29 then W (C (radix-1)) (radix-1) else
 W (V i) (if Nat.ltb i 10 then if sq:bool then smax i else imax
         else if Nat.leb 32 i && Nat.ltb i 42 then imax else word-1).
Definition pack s i := limbs (fun j => s (i+j)%nat).
Definition packE (s:nat->expr) i :=
 let d j:=s (i+j)%nat in
 Plus (d 0%nat) (Times (C radix) (Plus (d 1%nat) (Times (C radix)
 (Plus (d 2%nat) (Times (C radix) (Plus (d 3%nat) (Times (C radix) (d 4%nat)))))))).
Lemma pack_ok env s i : val env (packE s i) = pack (fun j=>val env (s j)) i.
Proof. reflexivity. Qed.

Definition check_kernel sq code :=
 let out:=arun code (initial sq) in
 forallb legal_instruction code &&
 forallb (fun i=>maximum (out i) <=? (if sq then smax i else omax i)) (seq 0 10) &&
 forallb (fun i=>congruent (packE (fun j=>term (out j)) i)
   (Times (packE V i) (packE V (if sq then i else (32+i)%nat)))) [0%nat;5%nat].
Theorem kernel_correct sq code :
 check_kernel sq code = true -> forall r,
 (forall j, models r (initial sq j) (r j)) ->
 let out:=run_kernel code r in
 (forall j, (j<10)%nat -> 0<=out j<=(if sq then smax j else omax j)) /\
 (forall i, (i=0%nat \/ i=5%nat) ->
 represents (pack out i) (pack r i * pack r (if sq then i else (32+i)%nat))).
Proof.
 unfold check_kernel; intros H r R. repeat rewrite Bool.andb_true_iff in H.
 destruct H as [[A B] Cc].
 assert (M:r 29%nat=radix-1) by (symmetry;exact (proj1 (R 29%nat))).
 pose proof (run_ok _ (rhs_memory r) _ _ _ (fun _=>eq_refl) M R A) as K.
 fold (run_kernel code r) in K.
 split.
 - intros j J. rewrite forallb_forall in B.
   specialize (B j ltac:(apply in_seq;lia)); apply Z.leb_le in B.
   destruct (K j) as [_ H]; lia.
 - intros i I. rewrite forallb_forall in Cc.
   specialize (Cc i ltac:(destruct I as [-> | ->];simpl;auto)). apply (congruent_ok r) in Cc.
   cbn [val] in Cc. rewrite !pack_ok in Cc.
   unfold pack, limbs in *. repeat setoid_rewrite (fun j=>proj1 (K j)) in Cc. exact Cc.
Qed.
