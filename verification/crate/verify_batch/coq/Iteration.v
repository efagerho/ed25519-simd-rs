From Coq Require Import List ZArith.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory.
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

Definition begin o text e cf:=option_map (LinkedRun.finish o (LinkedRun.initial o e cf))
 (StageEntry.observe o text e cf).

(* After scatter, R12 determines the next staging budget. The continuation
   carries all preceding stores, including the indices already published. *)
Inductive chain pol bias pc text e:nat -> cursor -> (nat->nat->bool) -> cursor -> Prop:=
 | done n p masks last:observed pol bias pc text e p masks (RejectExecution.BatchReturned last) ->
   chain pol bias pc text e n p masks last
 | more n p masks back next next_masks last:observed pol bias pc text e p masks (RejectExecution.NextChunk back) ->
   ChunkStaging.execute (bias+pc) text (n-8) back=Some next ->
   chain pol bias pc text e (n-8) next next_masks last ->
   chain pol bias pc text e n p masks last.

Definition native pol bias pc text e cf masks last:=exists p,
 begin (bias+pc) text e cf=Some p /\ chain pol bias pc text e (Scatter.count e) p masks last.

Lemma scalar_rejected pol bias pc text e cf masks s q:
 BatchScalar.observe pol bias (bias+pc) text e cf masks=Some s ->
 regs(machine s) 0%nat mod 2^32=0 ->
 RejectExecution.scalar_rejection pol bias pc text e cf masks=Some(RejectExecution.BatchReturned q) ->
 native pol bias pc text e cf masks q.
Proof.
 intros Scalar Zero End;unfold RejectExecution.scalar_rejection in End;rewrite Scalar in End;cbn [bind] in End;
 rewrite Zero,Z.eqb_refl in End.
 unfold BatchScalar.observe,BatchScalar.scalar_entry in Scalar.
 destruct(StageEntry.observe (bias+pc) text e cf) as [st|] eqn:Start;[|discriminate].
 set(p:=LinkedRun.finish (bias+pc) (LinkedRun.initial (bias+pc) e cf) st) in *.
 exists p;split;[unfold begin;now rewrite Start|apply done].
 exists(FirstDispatch.Completed q);split;[|reflexivity].
 unfold dispatch,ChunkScalar.execute,ChunkScalar.enter;cbn [bind] in Scalar;fold p in Scalar.
 destruct(BatchScalar.via_strict pol bias p) as [v|] eqn:Shim;[|discriminate].
 cbn [bind] in Scalar|-*;destruct(BatchScalar.to_scalar bias v) as [child|] eqn:Call;[|discriminate].
 cbn [bind] in Scalar|-*;rewrite Scalar;cbn [option_map bind];unfold after_scalar;rewrite Zero,Z.eqb_refl.
 change (RejectedPath.execute false pol bias pc text s=Some(RejectExecution.BatchReturned q)) in End;now rewrite End.
Qed.

Definition exit e q:=accounted e (Return.writable e) q /\ byte_memory (mem(machine q)) /\ regs(machine q) 0%nat=1 /\
 ip q=read_word (mem e) (Return.sp e) /\ regs(machine q) 4%nat=Return.sp e+8 /\ RejectFinish.callee_saved e (machine q).
