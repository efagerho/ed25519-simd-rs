From Coq Require Import ZArith Lia.
From Coqprime.elliptic Require GZnZ.
From Curve25519 Require Import Field.
From Curve25519.group Require Import PrimeField Affine Decompression.
From Ed25519Simd.VerifyBatch Require Import Policy.
From Ed25519Simd.VerifyBatch Require StrictOrderClear.
Local Open Scope Z_scope.

Lemma canonical_compression Q : compression Q mod 2^255<prime.
Proof.
 set (v:=GZnZ.val prime (y Q)).
 assert (Y:0<=v<prime).
 { unfold v;rewrite (GZnZ.inZnZ prime (y Q));apply Z.mod_pos_bound;unfold prime;lia. }
 unfold compression;fold v;destruct (parity(x Q)).
 - replace (v+2^255) with (v+1*2^255) by ring;rewrite Z.mod_add by lia.
   rewrite Z.mod_small;unfold prime in *;lia.
 - rewrite Z.add_0_r,Z.mod_small;unfold prime in *;lia.
Qed.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem screened e j : signature_accepts Dalek (HashLayout.row e j) -> StrictOrderClear.eligible e j.
Proof.
 intro A;pose proof(Lane.accepted_eligible _ _ A) as On.
 destruct A as [S [P [Decoded [Key [Eq Strong]]]]].
 lazymatch type of Eq with _=compression ?Q=>change (BatchDecode.original_encoding true e j=compression Q) in Eq end.
 split;[split;[exact On|rewrite Eq;apply canonical_compression]|].
 rewrite Eq;eexists;split;[apply Lane.decodes_compression|exact Strong].
Qed.
End Iteration.
