From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Ed25519Simd.VerifyBatch Require Import Policy Return BatchScalar BatchDecode.
From Ed25519Simd.VerifyBatch Require RejectExecution RejectedPath EligibleLanes TableValues.
Local Open Scope Z_scope.

Inductive boundary:=Completed (q:cursor) | MoreChunks (q:cursor) | BuildTables (q:cursor).
Definition after_reject r:=match r with RejectExecution.BatchReturned q=>Completed q | RejectExecution.NextChunk q=>MoreChunks q end.
Definition run pol bias pc text e c ks:=
 bind (BatchScalar.observe pol bias (bias+pc) text e c ks) (fun scalar=>
 if regs(machine scalar) 0%nat mod 2^32=?0 then option_map after_reject (RejectedPath.execute false pol bias pc text scalar)
 else bind (BatchDecode.enter bias scalar) (fun d=>bind (BatchScalar.masks_after pol bias (bias+pc) text e c ks) (fun bank=>
 bind (EligibleLanes.observe pol bias e d bank) (fun t=>let q:=EligibleLanes.stopped t in
 if regs(machine q) 14%nat=?0 then option_map after_reject (RejectedPath.execute true pol bias pc text q)
 else option_map BuildTables (TableValues.execute bias q))))).

Lemma scalar_path pol bias pc text e c ks s r : BatchScalar.observe pol bias (bias+pc) text e c ks=Some s ->
 regs(machine s) 0%nat mod 2^32=0 -> RejectExecution.scalar_rejection pol bias pc text e c ks=Some r ->
 run pol bias pc text e c ks=Some(after_reject r).
Proof.
 intros Steps Z;unfold run,RejectExecution.scalar_rejection;rewrite Steps;cbn [bind];rewrite Z,Z.eqb_refl.
 unfold RejectedPath.execute;cbn [option_map];intro X;unfold PrepareUnwind.unwind in X;now rewrite X.
Qed.
