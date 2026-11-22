From ProofArithmetic Require Import Interval.
From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.Blocks isa.Instructions.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Curve25519 Require Import FieldPolynomial.
From Ed25519Simd Require Import FieldSymbolic.
From Ed25519Simd Require Export FieldKernel.
From Ed25519Simd.CachedAdd Require Import Program.
Import ListNotations. Open Scope Z_scope.
Inductive kernel := PrepareAB | PrepareFG | PrepareEH | Independent | Pair | Single.
Definition kernel_id k := match k with PrepareAB=>0%nat | PrepareFG=>2%nat | PrepareEH=>3%nat |
 Independent=>10%nat | Pair=>11%nat | Single=>12%nat end.
Definition code k := fragment_code add_cached_program (kernel_id k).
Definition bias i := if Nat.eqb i 0 then 0x3fffffffffff6800 else 0x3ffffffffffff800.
Definition input_bound k i := if Nat.ltb i 10 then
 match k with PrepareFG=>folded_column_bound | PrepareAB | PrepareEH=>2^64-1 | Single=>if Nat.ltb i 5 then split-1 else 2^64-1 | _=>split-1 end else 2^64-1.
Definition needs_bias k := match k with PrepareAB | PrepareFG | PrepareEH=>true | _=>false end.
Definition initial k i :=
 if Nat.eqb i 28 then I(C 19)19 19 else
 if Nat.eqb i 29 then I(C(radix-1))(radix-1)(radix-1) else
 if needs_bias k && Nat.leb 30 i && Nat.ltb i 32 then I(C(bias(i-30)))(bias(i-30))(bias(i-30))
 else I(regvar i)0(input_bound k i).
Definition loads k (b:nat) d := I(memvar(Z.to_nat(d/64)))0
 (match k with PrepareEH=>folded_column_bound | _=>split-1 end).
Definition hints (k:kernel) : list interval := [].
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
 | Independent=>folded_column_bound | _=>output_bound i end.
Definition check_kernel k := FieldKernel.check_kernel
 (code k) (initial k) (hints k) (loads k) (output_starts k) (bound k) (target k).
Local Opaque code hints loads.
Theorem kernel_correct k : check_kernel k=true ->
 forall env load r,
 Forall (valid_hint env) (hints k) ->
 (forall b d, In (b,d) (loads_of (code k)) -> models env (loads k b d) (load b d)) ->
 (forall i, models env (initial k i) (r i)) ->
 forall start, In start (output_starts k) ->
 (forall i, (i<5)%nat -> 0<=run load (code k) r (start+i)%nat<=bound k (start+i)%nat) /\
 represents (pack (run load (code k) r) start) (val env (target k start)).
Proof.
 unfold check_kernel; intros Check env load r H M R.
 assert (Mask : r 29%nat = radix-1) by (symmetry; exact (proj1 (R 29%nat))).
 exact (FieldKernel.kernel_correct (code k) (initial k) (hints k) (loads k)
          (output_starts k) (bound k) (target k) Check env load r Mask H M R).
Qed.
Local Transparent code hints loads.

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
