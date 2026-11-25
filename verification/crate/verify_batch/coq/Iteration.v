From Coq Require Import List ZArith.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Ed25519Simd.VerifyBatch Require Import Policy.
From Ed25519Simd.VerifyBatch Require ChunkScalar FirstDispatch ScoreProgress ScoreDecision ScorePublish.
Local Open Scope Z_scope.

(* Each transition takes the cursor returned by the preceding call. The
   caller can observe any volatile register completion permitted by SHA. *)
Definition after_decode pol bias pc text e bank d:=
 bind (EligibleLanes.observe pol bias e d bank) (fun t=>let q:=EligibleLanes.stopped t in
 if regs(machine q) 14%nat=?0 then option_map FirstDispatch.after_reject (RejectedPath.execute true pol bias pc text q)
 else bind (ReadyDispatch.observe pol bias pc text e q (TableMask.masks t))
      (fun result=>FirstDispatch.continue pol bias pc text (fst result) (snd result))).
Definition after_scalar pol bias pc text e s bank:=
 if regs(machine s) 0%nat mod 2^32=?0 then option_map FirstDispatch.after_reject (RejectedPath.execute false pol bias pc text s)
 else bind (BatchDecode.enter bias s) (after_decode pol bias pc text e bank).
Definition dispatch pol bias pc text e p masks:=
 bind (ChunkScalar.execute pol bias p masks) (fun '(s,bank)=>after_scalar pol bias pc text e s bank).

Definition publish pol bias pc text screen last:=if ScoreProduct.rejected pol screen then
 ScorePublish.execute bias pc text screen=Some last
 else exists q,ScoreDecision.observed pol bias screen q /\ ScorePublish.scatter bias pc text q=Some last.
Definition score pol bias pc text h r last:=exists s cf child score screen,
 HashResume.compatible r s /\ well_formed s /\ ScoreCall.execute bias pc text h r s cf=Some child /\
 ScoreStart.from_call pol bias child=Some score /\ ScoreProgress.observed pol bias score screen /\
 publish pol bias pc text screen last.
Definition finish pol bias pc text sent last:=match sent with
 | FirstDispatch.Completed q=>last=RejectExecution.BatchReturned q
 | FirstDispatch.MoreChunks q=>last=RejectExecution.NextChunk q
 | FirstDispatch.HashReturned h r=>score pol bias pc text h r last end.
Definition observed pol bias pc text e p masks last:=exists sent,
 dispatch pol bias pc text e p masks=Some sent /\ finish pol bias pc text sent last.
