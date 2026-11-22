From Coq Require Import List ZArith Bool Lia.
From ProofArithmetic Require Import Interval.
From Machine Require Import isa.Instructions.
From Curve25519 Require Import Field Radix51 FieldPolynomial.
From Ed25519Simd Require Import FieldSymbolic.
Import ListNotations. Local Open Scope Z_scope.

(* A radix-51 column collects at most five low IFMA halves and twice
   five high halves. Folding one more column by 19 scales that bound by 20. *)
Definition folded_column_bound := 300 * split - 1.
Definition folded_columns := field_bound (fun _ => folded_column_bound).

Definition regvar i := V (2*i).
Definition memvar i := V (2*i+1).
Definition packE (s:nat->expr) i :=
 let d j:=s (i+j)%nat in
 Plus (d 0%nat) (Times (C radix) (Plus (d 1%nat) (Times (C radix)
 (Plus (d 2%nat) (Times (C radix) (Plus (d 3%nat) (Times (C radix) (d 4%nat)))))))).
Definition pack r i := limbs (fun j=>r (i+j)%nat).
Lemma pack_ok env s i : val env (packE s i)=pack (fun j=>val env (s j)) i.
Proof. reflexivity. Qed.
Definition minus a b := Plus a (Times (C (-1)) b).
(* The routine supplies its decoded block, symbolic inputs, valid hints,
   output register groups, limb bounds and target field expressions. *)
Section Check.
Variables (code : list instruction) (initial : nat -> interval)
          (hints : list interval) (loads : nat -> Z -> interval)
          (output_starts : list nat) (bound : nat -> Z) (target : nat -> expr).
Let result := arun hints loads code initial.
Definition check_kernel :=
 forallb legal_instruction code &&
 forallb (fun start=>
  forallb (fun i=> (0<=?lower(result (start+i)%nat)) &&
    (upper(result (start+i)%nat) <=? bound (start+i)%nat)) (seq 0 5) &&
  congruent (packE (fun i=>term (result i)) start) (target start)) output_starts.
Theorem kernel_correct : check_kernel =true ->
 forall env load r, r 29%nat=radix-1 ->
 Forall (valid_hint env) hints ->
 (forall b d, In (b,d) (loads_of code) -> models env (loads b d) (load b d)) ->
 (forall i, models env (initial i) (r i)) ->
 forall start, In start output_starts ->
 (forall i, (i<5)%nat -> 0<=run load code r (start+i)%nat<=bound (start+i)%nat) /\
 represents (pack (run load code r) start) (val env (target start)).
Proof.
 unfold check_kernel;rewrite andb_true_iff;intros [Legal Check] env load r Mask H M R start S.
 pose proof (run_ok env hints loads load code initial r H M Mask R Legal) as Run.
 change (forall i, models env (result i) (run load code r i)) in Run.
 rewrite forallb_forall in Check;specialize (Check start S).
 apply andb_true_iff in Check as [Bounds Congruence];split.
 - intros i I;rewrite forallb_forall in Bounds;specialize (Bounds i ltac:(apply in_seq;lia)).
   apply andb_true_iff in Bounds as [L U];apply Z.leb_le in L;apply Z.leb_le in U.
   destruct (Run (start+i)%nat) as [_ B];lia.
 - apply (congruent_ok env) in Congruence;rewrite pack_ok in Congruence.
   unfold pack,limbs in *;repeat setoid_rewrite (fun i=>proj1 (Run i)) in Congruence.
   exact Congruence.
Qed.
End Check.
