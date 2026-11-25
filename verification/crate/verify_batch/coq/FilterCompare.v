From Coq Require Import List ZArith Lia Bool.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.QwordBlock execution.MappedFetch memory.ByteMemory memory.FlatMemory.
From Machine Require execution.PredicateBlock execution.MaskedWords execution.MaskTransfer.
From Curve25519 Require Import Radix51.
From Ed25519Simd.Decode Require Limbs.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require PointCompare.
Import ListNotations. Local Open Scope Z_scope.

Definition start phase:=PointCompare.start (PointCompare.Key phase).
Definition result phase:=PointCompare.result (PointCompare.Key phase).
Definition pc phase:=PointCompare.pc (PointCompare.Key phase).
Definition writes phase:=PointCompare.writes (PointCompare.Key phase).
Definition words phase:=PointCompare.words (PointCompare.Key phase).
Definition registers phase:=PointCompare.registers (PointCompare.Key phase).
Definition memory_after phase:=PointCompare.memory_after (PointCompare.Key phase).
Definition history phase:=PointCompare.history (PointCompare.Key phase).
Definition high_regs phase:=PointCompare.high_regs (PointCompare.Key phase).
Definition equal_zero phase:=PointCompare.equal_zero (PointCompare.Key phase).
Definition execute:=PointCompare.execute (PointCompare.Key false).

Theorem checked phase bias e p bank : loaded Dalek bias (mem e) (writable e) -> ip p=bias+FilterLoad.site+start phase ->
 accounted e (writable e) p -> well_formed(machine p) -> (forall j,vectors(machine p) j 29%nat=radix-1) ->
 exists q k,execute bias p bank=Some(q,k) /\ result phase bias e p q k.
Proof. exact (PointCompare.checked (PointCompare.Key phase) bias e p bank). Qed.
