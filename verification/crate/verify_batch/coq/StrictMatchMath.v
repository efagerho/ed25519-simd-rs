From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.Dependencies execution.VectorProcedure.
From Curve25519 Require Import Radix51.
From Curve25519.group Require Import PrimeField.
From Ed25519Simd.Decode Require Import Kernels Power.
From Curve25519 Require Import Radix51Digits.
From Ed25519Simd.Decode Require Import Decode.
From Ed25519Simd.Dalek Require FieldOps.
From Ed25519Simd.DalekPostHash Require Decoded.
From Ed25519Simd.VerifyBatch Require StrictSeeded.
Local Open Scope Z_scope.
Local Notation kernel:=DecoderProduct.kernel.
Definition suffix:=StrictSeeded.code++DecoderKernel.body DecoderKernel.Carry.
Definition prepared r a z c:=forall i,(i<5)%nat ->
 r i=a i /\ r (5+i)%nat=z i /\ r (10+i)%nat=
 Arithmetic.vpsubq (DecoderFrame.constant (if Nat.eqb i 0 then 2 else 3)) (c i).
Definition constants r:=forall i,(i<4)%nat -> r (28+i)%nat=DecoderFrame.constant i.
Definition live i:=((i<?15) || ((28<=?i)&&(i<?32)))%nat.
Lemma depends:forall i,(i<5)%nat -> agreement (fun _ _=>false) suffix live i=true.
Proof. intros [|[|[|[|[|i]]]]] K;try lia;vm_compute;reflexivity. Qed.

Lemma initial r a z c:prepared r a z c -> constants r -> forall i,live i=true ->
 r i=Instructions.run no_read Dalek.FieldOps.seeds (Dalek.FieldOps.inputs a z c) i.
Proof.
 intros R C;pose proof(R 0%nat ltac:(lia)) as [A0 [Z0 Y0]];pose proof(R 1%nat ltac:(lia)) as [A1 [Z1 Y1]].
 pose proof(R 2%nat ltac:(lia)) as [A2 [Z2 Y2]];pose proof(R 3%nat ltac:(lia)) as [A3 [Z3 Y3]].
 pose proof(R 4%nat ltac:(lia)) as [A4 [Z4 Y4]].
 pose proof(C 0%nat ltac:(lia)) as C0;pose proof(C 1%nat ltac:(lia)) as C1;
 pose proof(C 2%nat ltac:(lia)) as C2;pose proof(C 3%nat ltac:(lia)) as C3.
 intros i On;unfold live in On;apply orb_true_iff in On;rewrite andb_true_iff in On.
 repeat rewrite Nat.ltb_lt in On;rewrite Nat.leb_le in On.
 do 32 (destruct i as [|i];[first [assumption|lia]|]);lia.
Qed.

Lemma projection r a z c : prepared r a z c -> constants r -> forall i,(i<5)%nat ->
 Instructions.run no_read suffix r i=Dalek.FieldOps.subtract_product kernel a z c i.
Proof.
 intros R C i K;unfold Dalek.FieldOps.subtract_product,Dalek.FieldOps.fused;rewrite run_app.
 change (Instructions.run no_read suffix r i=Instructions.run no_read
  (StrictSeeded.seed++DecoderKernel.body DecoderKernel.Convolve++DecoderKernel.body DecoderKernel.Fold++DecoderKernel.body DecoderKernel.Carry)
  (Instructions.run no_read Dalek.FieldOps.seeds (Dalek.FieldOps.inputs a z c)) i).
 unfold suffix,StrictSeeded.code;rewrite <-!app_assoc.
 exact (agreement_sound (fun _ _=>false) suffix live _ _ _ _ (fun _ _ _=>eq_refl) (initial _ _ _ _ R C) i (depends i K)).
Qed.
Lemma keeps_constants r : constants r -> constants (Instructions.run no_read suffix r).
Proof.
 intros C i K;rewrite <- (C i K);apply untouched;destruct i as [|[|[|[|i]]]];try lia;vm_compute;reflexivity.
Qed.
Lemma kernel_checked:Dalek.FieldOps.checked kernel=true.
Proof. vm_compute;reflexivity. Qed.

Theorem match_coord r a z c:prepared r a z c -> constants r -> split_field a -> split_field z -> split_field c ->
 (high_test (Instructions.run no_read suffix r) 0=true <-> (value a*value z)%fp=value c).
Proof.
 intros R C A Z Y;rewrite <-(DalekPostHash.Decoded.match_ok kernel a z c kernel_checked A Z Y).
 unfold DalekPostHash.Decoded.match_coord,high_test;now repeat rewrite (projection _ _ _ _ R C) by lia.
Qed.
