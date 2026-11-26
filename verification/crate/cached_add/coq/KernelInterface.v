From ProofArithmetic Require Import Interval.
From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordBounds.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd Require Export FieldKernel.
From Curve25519 Require Import FieldPolynomial.
From Ed25519Simd Require Import FieldSymbolic.
From Ed25519Simd.CachedAdd Require Import Kernels.
Import ListNotations. Open Scope Z_scope.
Definition operands k r :=
 (forall i,(i<10)%nat ->0<=r i<=input_bound k i) /\
 r 28%nat=19 /\ r 29%nat=radix-1 /\
 (needs_bias k=true -> r 30%nat=bias 0 /\ r 31%nat=bias 1).
Definition right_count k := match k with PrepareAB | PrepareEH | Independent=>10%nat | PrepareFG | CarryY=>0%nat | _=>5%nat end.
Definition right_bound k := match k with PrepareAB | PrepareEH=>folded_column_bound | _=>split-1 end.
Definition right_ok k m := forall i,(i<right_count k)%nat ->0<=m i<=right_bound k.
Definition load_base k := match k with PrepareAB=>7%nat | PrepareEH=>9%nat | _=>8%nat end.
Local Opaque code check_kernel.
Theorem all_kernels_checked k : check_kernel k=true.
Proof.
 destruct k.
 - exact PrepareAB_checked.
 - exact PrepareFG_checked.
 - exact PrepareEH_checked.
 - exact Independent_checked.
 - exact Pair_checked.
 - exact Single_checked.
 - exact CarryY_checked.
Qed.
Lemma initial_models k r m : (forall i, word64 (r i)) -> operands k r ->
 forall i, models (env r m) (initial k i) (r i).
Proof.
 intros Words [Bounds [C [Mask Bias]]] i.
 unfold initial. destruct (Nat.eqb i 28) eqn:E.
 - apply Nat.eqb_eq in E;subst;unfold models;cbn [term lower upper val ProofArithmetic.Interval.I enclosure lower_bound upper_bound];rewrite C;lia.
 - destruct (Nat.eqb i 29) eqn:M.
   + apply Nat.eqb_eq in M;subst;unfold models;cbn [term lower upper val ProofArithmetic.Interval.I enclosure lower_bound upper_bound];rewrite Mask;lia.
   + destruct (needs_bias k && Nat.leb 30 i && Nat.ltb i 32) eqn:B.
     * repeat rewrite andb_true_iff in B;destruct B as [[K L] U].
       apply Nat.leb_le in L;apply Nat.ltb_lt in U.
       assert (i=30%nat \/ i=31%nat) by lia. destruct (Bias K) as [A B].
       destruct H as [-> | ->];unfold models;cbn [term lower upper val Nat.sub ProofArithmetic.Interval.I enclosure lower_bound upper_bound];rewrite ?A,?B;lia.
     * unfold models;cbn [term lower upper ProofArithmetic.Interval.I enclosure lower_bound upper_bound];rewrite env_reg;split;[reflexivity|].
       destruct (Nat.ltb i 10) eqn:I.
       -- apply Nat.ltb_lt in I;apply Bounds;exact I.
       -- unfold input_bound;rewrite I. specialize (Words i);unfold word64 in *;lia.
Qed.
Lemma valid_hints k r m : (forall i, word64 (r i)) -> operands k r ->
 Forall (valid_hint (env r m)) (hints k).
Proof. intros;constructor. Qed.
Lemma load_indices k : aligned_loads (code k) (load_base k) (right_count k)=true.
Proof. destruct k;vm_compute;reflexivity. Qed.
Lemma loads_models k r load m : right_ok k m ->
 (forall i, (i<right_count k)%nat -> load (load_base k) (64*Z.of_nat i)=m i) ->
 forall b d, In (b,d) (loads_of(code k)) -> models (env r m) (loads k b d) (load b d).
Proof. apply (aligned_loads_model _ _ _ _ _ _ _ (load_indices k)). Qed.
Theorem run_correct k r load m start :
 (forall i, word64(r i)) -> operands k r -> right_ok k m ->
 (forall i, (i<right_count k)%nat -> load (load_base k) (64*Z.of_nat i)=m i) ->
 In start (output_starts k) ->
 (forall i, (i<5)%nat -> 0<=run load (code k) r (start+i)%nat<=bound k (start+i)%nat) /\
 represents (pack (run load (code k) r) start) (val (env r m) (target k start)).
Proof.
 intros W Input Right Mem Start; eapply kernel_correct;
 eauto using all_kernels_checked,initial_models,valid_hints,loads_models.
Qed.
