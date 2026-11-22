From ProofArithmetic Require Import Interval.
From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.Blocks isa.Instructions.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Curve25519 Require Import FieldPolynomial.
From Ed25519Simd Require Import FieldSymbolic.
From Ed25519Simd Require Export FieldKernel.
From Ed25519Simd.Double4 Require Import Program.
From Curve25519 Require Export Radix51.
Import ListNotations. Open Scope Z_scope.
Inductive kernel := AddReduce | SquarePair | SubtractReduce | MultiplyPair | MultiplySingle.
Definition kernel_pc k := match k with
 | AddReduce=>add_reduce_pc | SquarePair=>square_pair_pc
 | SubtractReduce=>subtract_reduce_pc | MultiplyPair=>multiply_pair_pc | MultiplySingle=>multiply_single_pc end.
Definition code k := match lookup (sections double4_program) (kernel_pc k) with
 | Some b=>flat_map (fun op=>match op with VectorCode id=>fragment_code double4_program id | _=>[] end) (body b)
 | None=>[] end.
Definition bias i := if Nat.eqb i 0 then 0x3fffffffffff6800 else 0x3ffffffffffff800.
Definition input_bound k i :=
 if Nat.ltb i 10 then match k with
 | AddReduce | SquarePair=>loose_bound i
 | SubtractReduce=>folded_column_bound
 | _=>split-1 end else 2^64-1.
Definition initial k i :=
 if Nat.eqb i 28 then I (C 19) 19 19 else
 if Nat.eqb i 29 then I (C (radix-1)) (radix-1) (radix-1) else
 if match k with SubtractReduce=>Nat.leb 30 i && Nat.ltb i 32 | _=>false end
 then I (C (bias (i-30))) (bias (i-30)) (bias (i-30)) else
 I (regvar i) 0 (input_bound k i).
Definition loads k (b:nat) d := I (memvar (Z.to_nat (d/64))) 0
 (match k with SubtractReduce=>folded_column_bound | _=>split-1 end).
Definition hints k := match k with SquarePair=>
 map (fun i=>I (Plus (regvar (S i)) (Quot (regvar i) radix)) 0 (split-1)) [0%nat;5%nat]
 | _=>[] end.
Definition target k start := match k with
 | AddReduce=>Plus (packE regvar 0) (packE regvar 5)
 | SquarePair=>Times (packE regvar start) (packE regvar start)
 | MultiplyPair | MultiplySingle=>Times (packE regvar start) (packE memvar 0)
 | SubtractReduce=>
   let a:=packE memvar 0 in let b:=packE memvar 5 in
   if Nat.eqb start 0 then minus (packE regvar 5) (Plus a b) else
   if Nat.eqb start 5 then Times (C (-1)) (Plus a b) else
   if Nat.eqb start 10 then minus b a else minus (minus b a) (Times (C 2) (packE regvar 0)) end.
Definition output_starts k := match k with
 | AddReduce=>[10%nat] | SubtractReduce=>[0%nat;5%nat;10%nat;15%nat]
 | MultiplySingle=>[0%nat] | _=>[0%nat;5%nat] end.
Definition bound k i := match k with
 | AddReduce | SubtractReduce | MultiplySingle=>ready_bound
 | SquarePair=>folded_column_bound | _=>output_bound i end.
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

Theorem add_reduce_checked : check_kernel AddReduce=true.
Proof. vm_compute;reflexivity. Qed.
Theorem square_pair_checked : check_kernel SquarePair=true.
Proof. vm_compute;reflexivity. Qed.
Theorem subtract_reduce_checked : check_kernel SubtractReduce=true.
Proof. vm_compute;reflexivity. Qed.
Theorem multiply_pair_checked : check_kernel MultiplyPair=true.
Proof. vm_compute;reflexivity. Qed.
Theorem multiply_single_checked : check_kernel MultiplySingle=true.
Proof. vm_compute;reflexivity. Qed.
