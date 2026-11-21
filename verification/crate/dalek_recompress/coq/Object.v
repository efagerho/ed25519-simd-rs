From Coq Require Import ZArith Lia Bool.
From Machine Require Import execution.MaskTrace.
From Curve25519 Require Import Radix51.
From Curve25519.group Require Import Affine.
From Ed25519Simd.SmallOrder Require Audit EntryBytes Object.
From Ed25519Simd.Decode Require Import Kernels Program Unpack.
From Ed25519Simd.Decode Require DecoderBytes HelperBytes.
From Ed25519Simd.Dalek Require Import FieldOps Encoding Masks Batch Schedule Audit ObjectBytes.
Local Open Scope Z_scope.

Local Opaque MaskTrace.result SmallOrder.Audit.run_at execute returned packed.

Theorem assembled_dalek_recompress_correct : recompress_contract
 ObjectBytes.address ObjectBytes.symbol_bytes DecoderBytes.address DecoderBytes.symbol_bytes
 HelperBytes.address HelperBytes.symbol_bytes EntryBytes.address EntryBytes.symbol_bytes.
Proof.
 constructor.
 - vm_compute;reflexivity.
 - vm_compute;repeat split;reflexivity.
 - exact Object.assembled_small_order_correct.
 - exists code. split;[vm_compute;repeat split;reflexivity|].
   split;[intro op;apply frame_ok;destruct op;vm_compute;reflexivity|].
   split;[apply field_frame_ok;vm_compute;reflexivity|].
   intros n flat pts enc P pad initial N _ Bytes Pad Points.
   set (call:=small_call EntryBytes.address HelperBytes.address flat pts pad initial).
   set (masks:=fun i=>match call i with Some m=>m | None=>0 end).
   assert (Small:forall i,(i<n)%nat -> call i=Some(masks i) /\ 0<=masks i<256 /\
     forall j,(j<8)%nat ->
     (Z.testbit(masks i)(Z.of_nat j)=true <-> multiple 8 (P i j)=identity)).
   { intros i I. destruct(Points i I) as [B Rep].
     assert (XY:SmallOrder.Audit.bounded(point_words flat pts i))
       by (intros row j R J;apply B;lia).
     destruct(SmallOrder.Audit.run_correct _ _ _ _ Object.assembled_small_order_correct pad _
       (initial i) Pad XY) as [m [Run [Range Bits]]].
     change (call i=Some m) in Run. unfold masks;rewrite Run. split;[reflexivity|split;auto].
     intros j J. exact (proj2(Bits j J) (P i j) (Rep j J)). }
   exists (packed flat enc P masks n 0). split.
   + rewrite caller_returns by exact N. refine (batch_correct code flat pts enc call P masks _ _ Bytes n Points _ n (Nat.le_refl n)).
     * vm_compute;reflexivity.
     * intro op;destruct op;vm_compute;reflexivity.
     * intros i I;destruct (Small i I) as [E [B _]];auto.
   + split;[apply packed_range|]. intros i j I J;rewrite packed_bit by assumption.
     unfold expected;rewrite andb_true_iff, Z.eqb_eq,negb_true_iff.
     destruct(Small i I) as [_ [_ Bits]]. specialize (Bits j J).
     destruct (Z.testbit (masks i)(Z.of_nat j));intuition congruence.
Qed.
