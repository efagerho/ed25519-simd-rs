From Coq Require Import List ZArith Bool Lia.
From Curve25519 Require Import Field Radix51.
From Machine Require Import isa.Instructions execution.MaskTrace execution.CircuitFacts.
From ProofArithmetic Require Import Expressions.
From Ed25519Simd.field51 Require Import Zero Arithmetic Check.
Import ListNotations. Local Open Scope Z_scope.

From Ed25519Simd.field51 Require Export RootMasks.
From Ed25519Simd.Torsion Require Import Schedule.

Definition early_cut := Cut 155 (minus (Times px ry) (Times py rx)) FirstPositive.
Lemma early_checked : verify input_used [(160%nat,early_cut)] short O (fun _=>None)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma ordered_paths : ordered O short=true /\ ordered O long=true.
Proof. vm_compute;auto. Qed.
Lemma early_shape : slice 160 6 short = zero_gates 155 160.
Proof. vm_compute;reflexivity. Qed.
Lemma long_shapes :
 slice 751 6 long=zero_gates 746 751 /\ slice 757 6 long=zero_gates 562 757 /\
 slice 809 6 long=zero_gates 789 809 /\ slice 816 6 long=zero_gates 804 816 /\
 nth_error long 763=Some(OrK (Wire 756)(Wire 762)) /\
 nth_error long 815=Some(OrK (Wire 763)(Wire 814)) /\
 nth_error long 822=Some(OrK (Wire 815)(Wire 821)).
Proof. vm_compute;repeat split. Qed.
