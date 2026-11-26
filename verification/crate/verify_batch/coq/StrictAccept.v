From Coq Require Import ZArith Lia.
From Curve25519 Require Import Field.
From Ed25519 Require Optimized.
From Ed25519Simd.VerifyBatch Require Import Policy.
From Ed25519Simd.VerifyBatch Require StrictOrderClear.
Local Open Scope Z_scope.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem screened e j : signature_accepts Dalek (HashLayout.row e j) -> StrictOrderClear.eligible e j.
Proof.
 intro A;pose proof(Optimized.accepted_eligible _ _ A) as On.
 destruct A as [_ [P [_ [R [_ [Eq [_ Strong]]]]]]].
 change (BatchDecode.original_encoding true e j=compression R) in Eq.
 split;[split;[exact On|rewrite Eq;rewrite compression_y; apply (proj2 (y_range _))]|].
 rewrite Eq;eexists;split;[apply PointEncoding.decodes_compression|exact Strong].
Qed.
End Iteration.
