From Coq Require Import List ZArith.
From Machine Require execution.Composition.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory.
From Ed25519Simd.VerifyBatch Require Import Policy.
From Ed25519Simd.VerifyBatch Require ChunkScalar FirstDispatch ScoreProgress ScoreDecision ScorePublish.
Local Open Scope Z_scope.

(* Each transition takes the cursor returned by the preceding call. The
   caller can observe any volatile register completion permitted by SHA. *)
Definition publish pol bias pc text screen last:=if ScoreProduct.rejected pol screen then
 ScorePublish.execute bias pc text screen=Some last
 else Composition.followed_by (ScoreDecision.observed pol bias screen)
   (fun q => Composition.output (ScorePublish.scatter bias pc text q)) last.
Definition score pol bias pc text h r :=
 Composition.followed_by (ScoreStart.from_hash pol bias pc text h r) (fun started =>
   Composition.followed_by (ScoreProgress.observed pol bias started) (publish pol bias pc text)).
Definition finish pol bias pc text sent last:=match sent with
 | FirstDispatch.Completed q=>last=RejectExecution.BatchReturned q
 | FirstDispatch.MoreChunks q=>last=RejectExecution.NextChunk q
 | FirstDispatch.HashReturned h r=>score pol bias pc text h r last end.
Definition observed pol bias pc text e p masks :=
 Composition.followed_by (Composition.output (FirstDispatch.dispatch pol bias pc text e p masks)) (finish pol bias pc text).

(* After scatter, R12 determines the next staging budget. The continuation
   carries all preceding stores, including the indices already published. *)
Inductive chain pol bias pc text e:nat -> cursor -> (nat->nat->bool) -> cursor -> Prop:=
 | done n p masks last:observed pol bias pc text e p masks (RejectExecution.BatchReturned last) ->
   chain pol bias pc text e n p masks last
 | more n p masks back next next_masks last:observed pol bias pc text e p masks (RejectExecution.NextChunk back) ->
   ChunkStaging.execute (bias+pc) text (n-8) back=Some next ->
   chain pol bias pc text e (n-8) next next_masks last ->
   chain pol bias pc text e n p masks last.

Definition native pol bias pc text e cf masks :=
 Composition.followed_by (Composition.output (StageEntry.begin (bias+pc) text e cf))
   (fun p => chain pol bias pc text e (Scatter.count e) p masks).

Lemma scalar_rejected pol bias pc text e cf masks s q:
 BatchScalar.observe pol bias (bias+pc) text e cf masks=Some s ->
 regs(machine s) 0%nat mod 2^32=0 ->
 RejectExecution.scalar_rejection pol bias pc text e cf masks=Some(RejectExecution.BatchReturned q) ->
 native pol bias pc text e cf masks q.
Proof.
 intros Scalar Zero End;unfold RejectExecution.scalar_rejection in End;rewrite Scalar in End;cbn [bind] in End;
 rewrite Zero,Z.eqb_refl in End.
 destruct (ChunkScalar.first_execution _ _ _ _ _ _ _ _ Scalar) as [p [bank [Start [Call _]]]].
 exists p;split;[exact Start|apply done].
 exists(FirstDispatch.Completed q);split;[|reflexivity].
 unfold FirstDispatch.dispatch;rewrite Call;cbn [bind];unfold FirstDispatch.after_scalar;rewrite Zero,Z.eqb_refl.
 change (RejectedPath.execute false pol bias pc text s=Some(RejectExecution.BatchReturned q)) in End;now rewrite End.
Qed.

Definition exit e q:=accounted e (Return.writable e) q /\ byte_memory (mem(machine q)) /\ regs(machine q) 0%nat=1 /\
 ip q=read_word (mem e) (Return.sp e) /\ regs(machine q) 4%nat=Return.sp e+8 /\ RejectFinish.callee_saved e (machine q).
