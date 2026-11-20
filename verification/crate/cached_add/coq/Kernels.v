From ProofArithmetic Require Import Interval.
From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks Instructions.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Curve25519 Require Import FieldPolynomial.
From Ed25519Simd Require Import FieldSymbolic.
From Ed25519Simd.CachedAdd Require Import Program.
Import ListNotations. Open Scope Z_scope.
Inductive kernel := PrepareAB | PrepareFG | PrepareEH | Independent | Pair | Single.
Definition kernel_id k := match k with PrepareAB=>0%nat | PrepareFG=>2%nat | PrepareEH=>3%nat |
 Independent=>10%nat | Pair=>11%nat | Single=>12%nat end.
Definition code k := fragment_code add_cached_program (kernel_id k).
Definition bias i := if Nat.eqb i 0 then 0x3fffffffffff6800 else 0x3ffffffffffff800.
Definition loose_bound i := if Nat.eqb (i mod 5) 0 then 2^60-1 else 2^53-1.
Definition input_bound k i := if Nat.ltb i 10 then
 match k with PrepareFG=>loose_bound i | PrepareAB | PrepareEH=>2^64-1 | Single=>if Nat.ltb i 5 then split-1 else 2^64-1 | _=>split-1 end else 2^64-1.
Definition needs_bias k := match k with PrepareAB | PrepareFG | PrepareEH=>true | _=>false end.
Definition regvar i := V (2*i).
Definition memvar i := V (2*i+1).
Definition initial k i :=
 if Nat.eqb i 28 then I(C 19)19 19 else
 if Nat.eqb i 29 then I(C(radix-1))(radix-1)(radix-1) else
 if needs_bias k && Nat.leb 30 i && Nat.ltb i 32 then I(C(bias(i-30)))(bias(i-30))(bias(i-30))
 else I(regvar i)0(input_bound k i).
Definition loads k (b:nat) d := I(memvar(Z.to_nat(d/64)))0
 (match k with PrepareEH=>loose_bound(Z.to_nat(d/64)) | _=>split-1 end).
Definition hints (k:kernel) : list interval := [].
Definition packE (s:nat->expr) i :=
 let d j:=s (i+j)%nat in
 Plus (d 0%nat) (Times (C radix) (Plus (d 1%nat) (Times (C radix)
 (Plus (d 2%nat) (Times (C radix) (Plus (d 3%nat) (Times (C radix) (d 4%nat)))))))).
Definition pack r i := limbs (fun j=>r (i+j)%nat).
Lemma pack_ok env s i : val env (packE s i)=pack (fun j=>val env (s j)) i.
Proof. reflexivity. Qed.
Definition minus a b := Plus a (Times (C (-1)) b).
Definition target k start :=
 match k with
 | PrepareAB=>if Nat.eqb start 0 then minus(packE memvar 5)(packE memvar 0)
               else Plus(packE memvar 5)(packE memvar 0)
 | PrepareFG=>if Nat.eqb start 0 then minus(packE regvar 0)(packE regvar 5)
               else Plus(packE regvar 0)(packE regvar 5)
 | PrepareEH=>if Nat.eqb start 0 then minus(packE memvar 5)(packE memvar 0)
               else Plus(packE memvar 5)(packE memvar 0)
 | Independent=>let src:=if Nat.eqb start 0 then 5%nat else 0%nat in
    Times(packE regvar src)(packE memvar src)
 | Pair | Single=>Times(packE regvar start)(packE memvar 0) end.
Definition output_starts k := match k with
 | PrepareFG | PrepareEH=>[0%nat;10%nat] | Single=>[0%nat] | _=>[0%nat;5%nat] end.
Definition bound k i := match k with
 | PrepareAB | PrepareFG | PrepareEH=>split-1
 | Independent=>loose_bound i | _=>output_bound i end.
Definition result k := arun(hints k)(loads k)(code k)(initial k).
Definition check_kernel k := forallb legal_instruction(code k) &&
 forallb(fun start=>forallb(fun i=>(0<=?lower(result k(start+i)%nat)) &&
 (upper(result k(start+i)%nat)<=?bound k(start+i)%nat))(seq 0 5) &&
 congruent(packE(fun i=>term(result k i))start)(target k start))(output_starts k).
Local Opaque code initial hints loads.
Theorem kernel_correct k : check_kernel k=true ->
 forall env load r,
 Forall (valid_hint env) (hints k) ->
 (forall b d, In (b,d) (loads_of (code k)) -> models env (loads k b d) (load b d)) ->
 (forall i, models env (initial k i) (r i)) ->
 forall start, In start (output_starts k) ->
 (forall i, (i<5)%nat -> 0<=run load (code k) r (start+i)%nat<=bound k (start+i)%nat) /\
 represents (pack (run load (code k) r) start) (val env (target k start)).
Proof.
 unfold check_kernel;rewrite andb_true_iff;intros [Legal Check] env load r H M R start S.
 assert (Mask:r 29%nat=radix-1) by (symmetry;exact (proj1 (R 29%nat))).
 pose proof (run_ok env (hints k) (loads k) load (code k) (initial k) r H M Mask R Legal) as Run.
 change (forall i, models env (result k i) (run load (code k) r i)) in Run.
 rewrite forallb_forall in Check;specialize (Check start S).
 apply andb_true_iff in Check as [Bounds Congruence];split.
 - intros i I;rewrite forallb_forall in Bounds;specialize (Bounds i ltac:(apply in_seq;lia)).
   apply andb_true_iff in Bounds as [L U];apply Z.leb_le in L;apply Z.leb_le in U.
   destruct (Run (start+i)%nat) as [_ B];lia.
 - apply (congruent_ok env) in Congruence;rewrite pack_ok in Congruence.
   unfold pack,limbs in *;repeat setoid_rewrite (fun i=>proj1 (Run i)) in Congruence.
   exact Congruence.
Qed.
Local Transparent code initial hints loads.
Theorem PrepareAB_checked : check_kernel PrepareAB=true.
Proof. vm_compute;reflexivity. Qed.
Theorem PrepareFG_checked : check_kernel PrepareFG=true.
Proof. vm_compute;reflexivity. Qed.
Theorem PrepareEH_checked : check_kernel PrepareEH=true.
Proof. vm_compute;reflexivity. Qed.
Theorem Independent_checked : check_kernel Independent=true.
Proof. vm_compute;reflexivity. Qed.
Theorem Pair_checked : check_kernel Pair=true.
Proof. vm_compute;reflexivity. Qed.
Theorem Single_checked : check_kernel Single=true.
Proof. vm_compute;reflexivity. Qed.
