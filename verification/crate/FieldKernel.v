From Coq Require Import List ZArith Bool Lia.
From ProofArithmetic Require Import Interval.
From Machine Require Import isa.Instructions.
From Curve25519 Require Import Field Radix51 FieldPolynomial.
From Ed25519Simd Require Import FieldSymbolic.
Import ListNotations. Local Open Scope Z_scope.

Definition regvar i := V (2*i).
Definition memvar i := V (2*i+1).
Definition packE (s:nat->expr) i :=
 let d j:=s (i+j)%nat in
 Plus (d 0%nat) (Times (C radix) (Plus (d 1%nat) (Times (C radix)
 (Plus (d 2%nat) (Times (C radix) (Plus (d 3%nat) (Times (C radix) (d 4%nat)))))))).
Definition pack r i := limbs (fun j=>r (i+j)%nat).
Lemma pack_ok env s i : val env (packE s i)=pack (fun j=>val env (s j)) i.
Proof. reflexivity. Qed.
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
Lemma pack_env_reg r m start : val (env r m) (packE regvar start)=pack r start.
Proof. change (limbs(fun i=>val (env r m) (regvar (start+i)))=pack r start).
 unfold limbs,pack;rewrite !env_reg;reflexivity. Qed.
Lemma pack_env_mem r m start : val (env r m) (packE memvar start)=pack m start.
Proof. change (limbs(fun i=>val (env r m) (memvar (start+i)))=pack m start).
 unfold limbs,pack;rewrite !env_mem;reflexivity. Qed.

Definition aligned_loads code base count :=
 forallb (fun bd => Nat.eqb (fst bd) base && (0<=?snd bd) && (snd bd mod 64 =? 0) &&
   Nat.ltb (Z.to_nat (snd bd/64)) count) (loads_of code).

Lemma aligned_loads_model code base count bound r m load :
 aligned_loads code base count=true ->
 (forall i, (i<count)%nat -> 0<=m i<=bound) ->
 (forall i, (i<count)%nat -> load base (64*Z.of_nat i)=m i) ->
 forall b d, In (b,d) (loads_of code) ->
 models (env r m) (I (memvar (Z.to_nat (d/64))) 0 bound) (load b d).
Proof.
 unfold aligned_loads;intros L R Mem b d Member.
 rewrite forallb_forall in L;specialize (L (b,d) Member);cbn [fst snd] in L.
 repeat rewrite andb_true_iff in L;destruct L as [[[Base D] Align] I].
 apply Nat.eqb_eq in Base;subst b. apply Z.leb_le in D;apply Z.eqb_eq in Align;apply Nat.ltb_lt in I.
 assert (Disp:d=64*Z.of_nat(Z.to_nat(d/64))).
 { rewrite Z2Nat.id by (apply Z.div_pos;lia). pose proof (Z.div_mod d 64 ltac:(lia));lia. }
 unfold models;cbn [term lower upper ProofArithmetic.Interval.I enclosure lower_bound upper_bound];rewrite env_mem.
 pose proof (Mem (Z.to_nat(d/64)) I) as E; rewrite <-Disp in E.
 rewrite E. split;[reflexivity|apply R;exact I].
Qed.

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
