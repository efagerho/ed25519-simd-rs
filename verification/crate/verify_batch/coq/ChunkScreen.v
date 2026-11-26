From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarWords memory.ByteMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Return Audit.
Local Open Scope Z_scope.

Section Window.
Context `{iteration:BatchWindow.t}.

(* Start at the actual scalar return. Both callers supply its register
   well-formedness and the mask bank passed to the decoder. *)
Theorem checked pol bias pc text e s bank : admissible pol bias pc text e -> StrictDispatch.bound pc text ->
 (0<BatchWindow.remaining e)%nat -> BatchScalar.post pol bias (bias+pc) e s ->
 (byte_memory (mem(machine s)) -> well_formed(machine s)) ->
 ScalarInputs.recoded e (machine s) /\
 (regs(machine s) 0%nat mod 2^32<>0 ->
   exists d,BatchDecode.enter bias s=Some d /\ BatchDecode.entry pol bias e d /\ BatchDecode.handoff pol e s d /\
     exists t,EligibleLanes.observe pol bias e d bank=Some t /\ EligibleLanes.checked_trace pol bias e d t /\
       EligibilityFrame.context pol bias (bias+pc) e (EligibleLanes.stopped t) /\
       (regs(machine(EligibleLanes.stopped t)) 14%nat=0 ->
         exists r,RejectedPath.execute true pol bias pc text (EligibleLanes.stopped t)=Some r /\ RejectExecution.post (bias+pc) e r)) /\
 (regs(machine s) 0%nat mod 2^32=0 ->
   exists r,RejectedPath.execute false pol bias pc text s=Some r /\ RejectExecution.post (bias+pc) e r).
Proof.
 intros A [_ [Scatter [Finish Extent]]] N Result Words;pose proof (BatchWindow.total e N) as Total.
 assert (Full:(0<Scatter.count e)%nat) by lia.
 destruct(batch_inputs _ _ _ _ _ A Full) as [P [[_ Slices] [[Range Sep] [_ [Idx _]]]]].
 pose proof(callee_image _ _ _ _ _ A Full) as I;pose proof(decoder_aligned _ _ _ _ _ A Full) as Al.
 pose proof Result as [PC [SP [Paid [Links [Outputs Data]]]]].
 destruct(Data N ltac:(intros j J;exact (proj1(proj2(Slices j J))))) as [Digits [Copy [Meta Saved]]].
 pose proof Copy as [Bytes [_ [_ [_ [_ [_ Layout]]]]]].
 specialize (Words Bytes).
 pose proof (fun decoded v => @RejectedPath.checked iteration decoded pol bias pc text e v Scatter Finish
   P I Range Extent (entry_text _ _ _ _ _ A) Sep N Idx) as Exit.
 split;[exact Digits|split].
 - intro Live.
   assert (Inputs:BatchDecode.readable e).
   { intros j sig J;destruct(Slices _ (BatchWindow.live_row e j N)) as [Key [Sig _]].
     unfold ScalarInputs.encoding_ptr;destruct sig;[|exact Key]. destruct Sig as [[L H] Away];split;[unfold MemoryGeometry.fits64;lia|intros x X;apply Away;lia]. }
   destruct(BatchDecode.from_return pol bias pc e s P I Inputs Result Copy Live) as [d [To [Entry Handoff]]].
   destruct(EligibleLanes.from_decoder _ _ _ s d bank P I Al Entry (segment_wf _ _ _ _ _ Words To) Digits (BatchDecode.caller_args _ _ _ _ Handoff))
     as [t [Run Check]].
   pose proof (EligibilityFrame.restore _ _ _ _ _ _ _ P Result Handoff Meta Saved Layout Check) as Frame.
   exists d;split;[exact To|split;[exact Entry|split;[exact Handoff|]]].
   exists t;split;[exact Run|split;[exact Check|split;[exact Frame|]]].
   intro Zero;apply (Exit true (EligibleLanes.stopped t) Frame (EligibleLanes.writes _ _ _ _ _ (proj2 Check))
     (EligibleLanes.words _ _ _ _ _ (proj2 Check)) (EligibleLanes.stack _ _ _ _ _ (proj2 Check))).
   + rewrite (EligibleLanes.destination _ _ _ _ _ (proj2 Check));unfold EligibleLanes.next;now rewrite Zero.
   + reflexivity.
 - intro Zero;exact (Exit false s (EligibilityFrame.Context _ _ _ _ _ Links Outputs Meta Saved Layout) Paid Words SP PC Zero).
Qed.
End Window.
