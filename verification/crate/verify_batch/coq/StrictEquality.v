From Coq Require Import ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls memory.ByteMemory.
From Curve25519.group Require Import Affine.
From Ed25519 Require Optimized.
From Ed25519Simd.VerifyBatch Require Import Policy Return.
From Ed25519Simd.VerifyBatch Require StrictAccept ScorePoint.
Local Open Scope Z_scope.

(* Once the canonical-Y and small-order screens have passed, equality of the
   two affine coordinates is exactly the strict encoded-signature test. *)
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem coordinates e j A R: StrictOrderClear.eligible e j ->
 decodes (little_endian(key_bytes(HashLayout.row e j))) A ->
 decodes (BatchDecode.original_encoding true e j) R ->
 (x(ScorePoint.product e j A)=x R /\ y(ScorePoint.product e j A)=y R <->
  signature_accepts Dalek (HashLayout.row e j)).
Proof.
 intros [[On Canon] [R' [DR' Strong]]] DA DR.
 destruct On as [S [_ [A' [DA' Key]]]].
 rewrite (decodes_unique _ _ _ DA' DA) in Key.
 rewrite (decodes_unique _ _ _ DR' DR) in Strong.
 apply Optimized.dalek_coordinates; try assumption; now apply Key.
Qed.
End Iteration.
