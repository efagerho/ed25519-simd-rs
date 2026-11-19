From ProofArithmetic Require Import Interval.
From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Instructions WordBounds.
Require Import FieldSpec Polynomial Symbolic Kernels.
Import ListNotations. Open Scope Z_scope.
Definition get (r:nat->Z) start := fun i=>(r (start+i)%nat).
Definition env (r m:nat->Z) i := if Nat.eqb (i mod 2) 0 then r (i/2)%nat else m (i/2)%nat.
Lemma env_reg r m i : val (env r m) (regvar i)=r i.
Proof.
 unfold regvar,val,env. replace (2*i)%nat with (i*2)%nat by lia.
 rewrite Nat.Div0.mod_mul,Nat.div_mul by lia;reflexivity.
Qed.
Lemma env_mem r m i : val (env r m) (memvar i)=m i.
Proof.
 unfold memvar,val,env.
 assert (D:((2*i+1)/2=i)%nat) by (symmetry;apply Nat.div_unique with (r:=1%nat);lia).
 assert (M:((2*i+1) mod 2=1)%nat) by (symmetry;apply Nat.mod_unique with (q:=i);lia).
 now rewrite D,M.
Qed.
Definition operands k r :=
 (forall i,(i<10)%nat ->0<=r i<=input_bound k i) /\
 r 28%nat=19 /\ r 29%nat=radix-1 /\
 (needs_bias k=true -> r 30%nat=bias 0 /\ r 31%nat=bias 1).
Definition right_count k := match k with PrepareAB | PrepareEH | Independent=>10%nat | PrepareFG=>0%nat | _=>5%nat end.
Definition right_bound k i := match k with PrepareEH=>loose_bound i | _=>split-1 end.
Definition right_ok k m := forall i,(i<right_count k)%nat ->0<=m i<=right_bound k i.
Definition load_base k := match k with PrepareAB=>7%nat | PrepareEH=>9%nat | _=>8%nat end.
Local Opaque code check_kernel.
Theorem all_kernels_checked k : check_kernel k=true.
Proof. destruct k; first [exact PrepareAB_checked | exact PrepareFG_checked | exact PrepareEH_checked | exact Independent_checked | exact Pair_checked | exact Single_checked]. Qed.
Lemma initial_models k r m : (forall i, word64 (r i)) -> operands k r ->
 forall i, models (env r m) (initial k i) (r i).
Proof.
 intros Words [Bounds [C [Mask Bias]]] i.
 unfold initial. destruct (Nat.eqb i 28) eqn:E.
 - apply Nat.eqb_eq in E;subst;unfold models;cbn [term lower upper val];rewrite C;lia.
 - destruct (Nat.eqb i 29) eqn:M.
   + apply Nat.eqb_eq in M;subst;unfold models;cbn [term lower upper val];rewrite Mask;lia.
   + destruct (needs_bias k && Nat.leb 30 i && Nat.ltb i 32) eqn:B.
     * repeat rewrite andb_true_iff in B;destruct B as [[K L] U].
       apply Nat.leb_le in L;apply Nat.ltb_lt in U.
       assert (i=30%nat \/ i=31%nat) by lia. destruct (Bias K) as [A B].
       destruct H as [-> | ->];unfold models;cbn [term lower upper val Nat.sub];rewrite ?A,?B;lia.
     * unfold models;cbn [term lower upper];rewrite env_reg;split;[reflexivity|].
       destruct (Nat.ltb i 10) eqn:I.
       -- apply Nat.ltb_lt in I;apply Bounds;exact I.
       -- unfold input_bound;rewrite I. specialize (Words i);unfold word64,word in *;lia.
Qed.
Lemma valid_hints k r m : (forall i, word64 (r i)) -> operands k r ->
 Forall (valid_hint (env r m)) (hints k).
Proof. intros;constructor. Qed.
Lemma load_indices k : forallb (fun bd=> Nat.eqb (fst bd) (load_base k) &&
 (0<=?snd bd) && (snd bd mod 64 =? 0) &&
 Nat.ltb (Z.to_nat(snd bd/64)) (right_count k)) (loads_of (code k))=true.
Proof. destruct k;vm_compute;reflexivity. Qed.
Lemma loads_models k r load m : right_ok k m ->
 (forall i, (i<right_count k)%nat -> load (load_base k) (64*Z.of_nat i)=m i) ->
 forall b d, In (b,d) (loads_of(code k)) -> models (env r m) (loads k b d) (load b d).
Proof.
 intros R Mem b d Member. pose proof (load_indices k) as L.
 rewrite forallb_forall in L;specialize (L (b,d) Member);cbn [fst snd] in L.
 repeat rewrite andb_true_iff in L;destruct L as [[[Base D] Align] I].
 apply Nat.eqb_eq in Base;subst b. apply Z.leb_le in D;apply Z.eqb_eq in Align;apply Nat.ltb_lt in I.
 assert (Disp:d=64*Z.of_nat(Z.to_nat(d/64))).
 { rewrite Z2Nat.id by (apply Z.div_pos;lia). pose proof (Z.div_mod d 64 ltac:(lia));lia. }
 unfold models,loads;cbn [term lower upper];rewrite env_mem.
 pose proof (Mem (Z.to_nat(d/64)) I) as E; rewrite <-Disp in E.
 rewrite E. split;[reflexivity|apply R;exact I].
Qed.
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
Lemma pack_env_reg r m start : val (env r m) (packE regvar start)=pack r start.
Proof. change (limbs(fun i=>val (env r m) (regvar (start+i)))=pack r start).
 unfold limbs,pack;rewrite !env_reg;reflexivity. Qed.
Lemma pack_env_mem r m start : val (env r m) (packE memvar start)=pack m start.
Proof. change (limbs(fun i=>val (env r m) (memvar (start+i)))=pack m start).
 unfold limbs,pack;rewrite !env_mem;reflexivity. Qed.
