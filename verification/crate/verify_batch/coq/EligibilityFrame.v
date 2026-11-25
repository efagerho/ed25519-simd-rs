From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.MemoryGeometry memory.FlatMemory memory.ByteMemory memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require BatchDecode DecoderSpills DecoderReturn EligibleLanes StageEntry IndexStores.
Local Open Scope Z_scope.

(* The eligibility store writes one byte between the prepared pointers and
   the scatter indices. Stack slots on either side still belong to the caller. *)
Definition live_byte pol e x:=common_top pol e-104<=x<sp e+8 /\ x<>Rows.frame e+840.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record context pol bias outer e q:Prop:=Context {
 links:return_slots pol bias outer e (mem(machine q));
 outputs:saved_outputs pol e (mem(machine q));
 metadata:BatchWindow.metadata e (mem(machine q));
 caller:StageEntry.saved_caller e (machine q);
 inputs:WrapperInputs.layout e (mem(machine q))
}.

Lemma frame_bytes pol bias e scalar d t :
 placement e -> BatchDecode.handoff pol e scalar d -> EligibleLanes.checked_trace pol bias e d t ->
 preserved (live_byte pol e) (mem(machine scalar)) (mem(machine(EligibleLanes.stopped t))).
Proof.
 intros P H [D Q] x [[Low High] Outside];destruct(scratch_stack _ P) as [Sep|Sep];
 pose proof(DecoderReturn.caller_memory _ _ _ _ _ D) as Kept;
 rewrite (EligibleLanes.memory_after _ _ _ _ _ Q);unfold EligibleLanes.store_at,commit;cbn [size address payload];
 rewrite write_outside by lia;rewrite Kept;[apply (BatchDecode.kept_bytes _ _ _ _ H)| |apply (BatchDecode.kept_bytes _ _ _ _ H)|].
 all: unfold DecoderSpills.caller_byte,DecoderSpills.top,span,common_top,Rows.frame,sp,disjoint in *.
 all: split;try (destruct pol;lia);intros sig;unfold BatchDecode.point,BatchDecode.point_offset;destruct sig,pol;lia.
Qed.

Theorem restore pol bias outer e scalar d t :
 placement e -> BatchScalar.post pol bias outer e scalar -> BatchDecode.handoff pol e scalar d ->
 BatchWindow.metadata e (mem(machine scalar)) -> StageEntry.saved_caller e (machine scalar) -> WrapperInputs.layout e (mem(machine scalar)) ->
 EligibleLanes.checked_trace pol bias e d t -> context pol bias outer e (EligibleLanes.stopped t).
Proof.
 intros P [_ [_ [_ [Links [Outputs _]]]]] H Meta [Slots BP] Layout C;pose proof(frame_bytes _ _ _ _ _ _ P H C) as Frame.
 destruct C as [D Q]. constructor.
 - eapply slots_preserved;[|exact Links];intros x X;apply Frame;unfold live_byte,common_top,Rows.frame,sp in *;destruct pol;lia.
 - eapply keep_saved_outputs;[|exact Outputs];intros x X;apply Frame;unfold live_byte,common_top,Rows.frame,sp in *;destruct pol;lia.
 - eapply IndexStores.metadata_preserved;[|exact Meta];intros x X;apply Frame;unfold live_byte,common_top,Rows.frame,sp in *;destruct pol;lia.
 - split;[intros x X;rewrite Frame;[apply Slots,X|unfold live_byte,common_top,Rows.frame,sp in *;destruct pol;lia]|].
   rewrite (EligibleLanes.kept_rbp _ _ _ _ _ Q),(DecoderReturn.restores _ _ _ _ _ D) by (cbn;tauto).
   now rewrite (BatchDecode.kept_rbp _ _ _ _ H).
 - eapply WrapperInputs.preserve;[|exact Layout];intros x X;apply Frame;unfold live_byte,WrapperInputs.needed,span,common_top,Rows.frame,sp in *;destruct pol;lia.
Qed.
End Iteration.
