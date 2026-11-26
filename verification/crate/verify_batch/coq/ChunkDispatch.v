From Coq Require Import List ZArith Lia.
From Machine Require execution.Composition.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarWords.
From Ed25519Simd.VerifyBatch Require Import Policy Image Return Audit Iteration.
From Ed25519Simd.VerifyBatch Require BatchWindow ChunkStaging ChunkScalar ChunkScreen.
Local Open Scope Z_scope.
Section Iteration.
Context `{iteration:BatchWindow.t}.

(* The branch condition is useful to first-window callers. The loop uses
   it to turn the zero bytes written on rejection into signature verdicts. *)
Definition post pol bias pc e b:=match b with
 | FirstDispatch.Completed q=> ~HashLayout.active pol e /\ RejectExecution.post (bias+pc) e (RejectExecution.BatchReturned q)
 | FirstDispatch.MoreChunks q=> ~HashLayout.active pol e /\ RejectExecution.post (bias+pc) e (RejectExecution.NextChunk q)
 | FirstDispatch.HashReturned q r=> HashLayout.active pol e /\ NativeHash.returned pol bias (bias+pc) e q r /\
     ScoreInputs.inputs pol e (machine q) /\ well_formed(machine q) end.

Local Lemma rejected_boundary pol bias pc e r : ~HashLayout.active pol e -> RejectExecution.post (bias+pc) e r ->
 post pol bias pc e (FirstDispatch.after_reject r).
Proof. destruct r;split;assumption. Qed.

Local Lemma scalar_inactive pol e s : ScalarInputs.recoded e s -> regs s 0%nat mod 2^32=0 -> ~HashLayout.active pol e.
Proof.
 intros [Bound Bits] Zero [j [J On]]. destruct (HashLayout.candidate_of _ _ _ On) as [Canon _].
 apply (proj2 (proj1 (Bits j J))) in Canon. rewrite Z.mod_small in Zero by lia;now rewrite Zero,Z.bits_0 in Canon.
Qed.

Definition invalid pol e:=forall j,(j<8)%nat -> (j<BatchWindow.remaining e)%nat ->
 ~signature_accepts pol (read_input (mem e) (regs e 7%nat) (BatchWindow.first+j)).
Lemma zeros pol e m:invalid pol e -> RejectExecution.zero_results e m -> ScoredChunk.outputs pol e m.
Proof. intros Bad Z j J;exists false;split;[apply Z,J|split;[discriminate|intro Sig;exfalso;exact (Bad j ltac:(lia) ltac:(lia) Sig)]]. Qed.

Lemma rejected_outputs pol bias pc e r : ~HashLayout.active pol e -> RejectExecution.post (bias+pc) e r ->
 RejectExecution.post_with (ScoredChunk.outputs pol e) (bias+pc) e r.
Proof.
 intros Inactive Done;eapply RejectExecution.post_map;[|exact Done].
 intros m Zeros;apply zeros;[|exact Zeros].
 intros j J Row Sig;apply Inactive;exists j;split;[exact J|apply Optimized.accepted_eligible].
 unfold HashLayout.row;now rewrite BatchWindow.own_row by exact Row.
Qed.

Local Lemma hash_call pol bias pc text e p q : admissible pol bias pc text e ->
 (0<BatchWindow.remaining e)%nat -> HashLayout.active pol e -> HashLayout.flags pol e (machine p) ->
 PreparedInputs.encodings e (machine p) -> ScoreInputs.inputs pol e (machine p) -> HashEntry.entry bias pc e p q ->
 exists b,FirstDispatch.hash_return bias q=Some b /\ post pol bias pc e b.
Proof.
 intros A N Live Flags Enc Inputs Child;pose proof (BatchWindow.total e N) as Total.
 assert (Full:(0<Scatter.count e)%nat) by lia.
 destruct(batch_inputs _ _ _ _ _ A Full) as [P [[_ Slices] [_ [_ [_ Entries]]]]].
 assert (Borrow:NativeHash.messages_immutable e).
 { intros j k J K;destruct(Slices _ (BatchWindow.live_row e j N)) as [_ [_ [_ B]]].
   apply B;unfold NativeHash.field in K|-*;lia. }
 destruct(@NativeHash.checked iteration pol bias pc e p q P (callee_image _ _ _ _ _ A Full) N
   (Entries BatchWindow.first (BatchWindow.remaining e) N Total)
   Borrow Live Flags Enc Child) as [r [Run Ret]].
 exists (FirstDispatch.HashReturned q r);split;[unfold FirstDispatch.hash_return;now rewrite Run|].
 exact (conj Live (conj Ret (conj (ScoreInputs.at_hash _ _ _ _ _ _ P Inputs Child) (HashEntry.words _ _ _ _ _ Child)))).
Qed.

Local Lemma after_eligible pol bias pc text e s d t : admissible pol bias pc text e -> StrictDispatch.bound pc text ->
 (0<BatchWindow.remaining e)%nat -> ScalarInputs.recoded e (machine s) ->
 BatchDecode.entry pol bias e d -> BatchDecode.handoff pol e s d -> EligibleLanes.checked_trace pol bias e d t ->
 EligibilityFrame.context pol bias (bias+pc) e (EligibleLanes.stopped t) ->
 (regs(machine(EligibleLanes.stopped t)) 14%nat=0 ->
   exists r,RejectedPath.execute true pol bias pc text (EligibleLanes.stopped t)=Some r /\ RejectExecution.post (bias+pc) e r) ->
 exists b,FirstDispatch.after_eligible pol bias pc text e t=Some b /\ post pol bias pc e b.
Proof.
 intros A Code N Digits Entry Handoff Check Frame Reject.
 pose proof (BatchWindow.total e N) as Total;assert (Full:(0<Scatter.count e)%nat) by lia.
 destruct(batch_inputs _ _ _ _ _ A Full) as [P [_ [[Range Sep] [Maps [Idx _]]]]].
 pose proof(callee_image _ _ _ _ _ A Full) as I;pose proof(decoder_aligned _ _ _ _ _ A Full) as Al.
 unfold FirstDispatch.after_eligible.
 destruct (Z.eqb_spec (regs(machine(EligibleLanes.stopped t)) 14%nat) 0) as [Zero|Yes].
 - destruct (Reject Zero) as [r [End Done]]. exists (FirstDispatch.after_reject r);split;[now rewrite End|].
   apply rejected_boundary;[|exact Done]. intros [j [J On]].
   apply (proj2(EligibleLanes.live_branch _ _ _ _ _ (proj2 Check)) ltac:(exists j;split;[exact J|apply (HashLayout.candidate_of _ _ _ On)])),Zero.
 - assert (Enc:PreparedInputs.operands e (machine(EligibleLanes.stopped t))).
   { eapply PreparedInputs.from_decoder;[exact P|exact Digits|exact Handoff| |exact Check].
     destruct Entry as [_ [_ [_ [_ [_ [_ [_ Data]]]]]]];exact Data. }
   destruct(PreparedReturn.from_eligible _ _ _ _ _ _ (TableMask.masks t) P I Al (proj2 Check) Frame (PreparedTables.input _ _ _ _ _ P Check) Enc Yes)
      as [q [k [Prep Done]]].
   destruct(ReadyDispatch.checked pol bias pc text e q k (proj1 Code) P I Range (entry_text _ _ _ _ _ A) Sep Done)
      as [v [kv [Go [_ Child]]]];unfold ReadyDispatch.observe;rewrite Prep;cbn [bind];rewrite Go;cbn [bind fst snd].
   pose proof(proj1(EligibleLanes.live_branch _ _ _ _ _ (proj2 Check)) Yes) as Active.
   destruct pol.
   * destruct Active as [j [J On]];assert (LiveZip:HashLayout.active Zip215 e) by (exists j;split;[exact J|now apply HashLayout.candidate]).
     apply (@hash_call Zip215 bias pc text e q v A N); [exact LiveZip|exact (HashLayout.zip_flags _ _ _ _ Done)|
       exact (PreparedReturn.encodings _ _ _ _ _ Done)|exact (ScoreInputs.zip _ _ _ _ Done)|exact Child].
   * destruct(StrictReturn.from_entry _ _ _ _ _ kv P I Maps Done Child) as [out [k0 [Filter F]]].
     destruct(@StrictDispatch.checked iteration bias pc text e v out k0 Code P I Range (entry_text _ _ _ _ _ A) Sep N Idx F)
       as [exit [Path [_ Branch]]];cbn [FirstDispatch.continue];rewrite Filter;cbn [bind];rewrite Path.
     assert (Eq:StrictReturn.live e (machine v) <-> HashLayout.active Dalek e).
     { split;intros [j [J H]];exists j;split;[exact J|apply (proj1(StrictReturn.strong_lane _ _ _ _ F j J)),H|
           exact J|apply (proj2(StrictReturn.strong_lane _ _ _ _ F j J)),H]. }
     destruct exit as [r|h];cbn [FirstDispatch.after_filter bind] in *;destruct Branch as [Survives Ready].
     -- exists (FirstDispatch.after_reject r);split;[reflexivity|apply rejected_boundary;[tauto|exact Ready]].
     -- apply (@hash_call Dalek bias pc text e out h A N); [exact (proj1 Eq Survives)|exact (HashLayout.strict_flags _ _ _ _ F)|
          exact (StrictReturn.encodings _ _ _ _ F)|exact (ScoreInputs.dalek _ _ _ _ F)|exact Ready].
Qed.

Theorem from_scalar pol bias pc text e s bank : admissible pol bias pc text e -> StrictDispatch.bound pc text ->
 (0<BatchWindow.remaining e)%nat -> BatchScalar.post pol bias (bias+pc) e s ->
 (ByteMemory.byte_memory (mem(machine s)) -> well_formed(machine s)) ->
 Composition.ensures (Composition.output (FirstDispatch.after_scalar pol bias pc text e s bank)) (post pol bias pc e).
Proof.
 intros A Code N Result Words. apply Composition.option_result.
 destruct (ChunkScreen.checked pol bias pc text e s bank A Code N Result Words) as [Digits [Decode Reject]].
 unfold FirstDispatch.after_scalar.
 destruct (Z.eqb_spec (regs(machine s) 0%nat mod 2^32) 0) as [Zero|Live].
 - destruct (Reject Zero) as [r [End Done]]. exists (FirstDispatch.after_reject r);split;[now rewrite End|].
   apply rejected_boundary;[|exact Done]. exact (scalar_inactive pol e _ Digits Zero).
 - destruct (Decode Live) as [d [To [Entry [Handoff [t [Run [Check [Frame Rejected]]]]]]]].
   rewrite To;cbn [bind];unfold FirstDispatch.after_decode;rewrite Run;cbn [bind].
   exact (after_eligible pol bias pc text e s d t A Code N Digits Entry Handoff Check Frame Rejected).
Qed.

Theorem checked pol bias pc text e p masks:admissible pol bias pc text e -> StrictDispatch.bound pc text ->
 (0<BatchWindow.remaining e)%nat ->
 ChunkStaging.entry (bias+pc) (BatchScalar.first_symbol pol-pc) e BatchWindow.first (BatchWindow.remaining e) p ->
 (forall x,BatchWindow.earlier e x -> mem(machine p) x=BatchWindow.before x) ->
 Composition.ensures (Composition.output (FirstDispatch.dispatch pol bias pc text e p masks)) (post pol bias pc e).
Proof.
 intros A Code N Stage Earlier;pose proof (BatchWindow.total e N) as Total.
 assert (Full:(0<Scatter.count e)%nat) by lia.
 destruct(batch_inputs _ _ _ _ _ A Full) as [P _].
 unfold FirstDispatch.dispatch.
 eapply LinkedRun.ensures_bind with (middle:=ChunkScalar.result pol bias pc e).
 - exact (ChunkScalar.checked pol bias pc e p masks P (callee_image _ _ _ _ _ A Full) Stage Earlier).
 - intros [s bank] [Result Words];exact (from_scalar pol bias pc text e s bank A Code N Result Words).
Qed.
End Iteration.
