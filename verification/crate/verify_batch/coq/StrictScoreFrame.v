From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.FlatMemory memory.ByteMemory memory.WriteTrace abi.SysV.
From Machine Require abi.FramePointer.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require ScoreTail StrictCandidateInputs.
Local Open Scope Z_scope.

Definition outputs e s:=regs s 13%nat=Rows.frame e+856 /\ regs s 14%nat=output e /\ regs s 15%nat=regs e 6%nat.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record context bias parent e caller p:Prop:=Context {
 frame:ScoreSaved.frame bias parent e caller (machine p);
 arguments:outputs e (machine p);
 at_tail:ip p=bias+ScoreSetup.callee Dalek+565 -> ScoreTail.arguments e 0 (machine p);
 candidate:regs(machine p) 12%nat<>0 -> StrictCandidateInputs.data e caller p
}.

Lemma keep_outputs e s u : outputs e s -> (forall g,In g sysv_saved -> regs u g=regs s g) -> outputs e u.
Proof. intros Out G;unfold outputs;rewrite (G 13%nat),(G 14%nat),(G 15%nat) by (simpl;tauto);exact Out. Qed.

Lemma at_call bias parent e h r caller score y t child :
 placement e -> ScoreStart.reached Dalek bias parent e h r caller score ->
 StrictRStart.reached bias e score y -> StrictRCanonical.result bias e y t ->
 StrictRCall.result e bias t child -> ScoreSaved.frame bias parent e caller (machine child) /\ outputs e (machine child).
Proof.
 intros P Start Y C Call;pose proof(StrictRFrame.checked _ _ _ _ _ _ _ _ _ P Start Y C) as F.
 pose proof(StrictRCall.saved _ _ _ _ Call) as G;split.
 - eapply ScoreSaved.keep with (s:=machine t).
   + eapply ScoreSaved.from_call;[exact (ScoreStart.caller _ _ _ _ _ _ _ _ Start)|exact (StrictRFrame.fp _ _ _ _ _ F)|exact (StrictRFrame.caller_frame _ _ _ _ _ F)].
   + apply G;simpl;tauto.
   + pose proof(StrictRCall.branch _ _ _ _ Call) as B;destruct (_=?0).
     * destruct B as [_ [M _]];intros x X;now rewrite M.
     * destruct B as [_ [_ [_ [_ [M _]]]]];intros x X;rewrite M;apply write_outside.
       pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)).
       unfold ScoreSaved.area,StrictRCall.call_store,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,Return.sp in *;cbn [qword address size];lia.
 - eapply keep_outputs;[exact (StrictRFrame.outputs _ _ _ _ _ F)|exact G].
Qed.

Lemma rejected bias parent e caller t call : ScoreSaved.frame bias parent e caller (machine call) ->
 outputs e (machine call) -> StrictRCall.rejected e bias t call -> regs(machine call) 12%nat=0 -> context bias parent e caller call.
Proof. intros F Out [_ [_ [_ [Z [DI [SI [DX _]]]]]]] Zero;constructor;[exact F|exact Out|intro PC;repeat split;assumption|contradiction]. Qed.

Lemma screened bias parent e caller child ret q : ScoreSaved.frame bias parent e caller (machine child) ->
 outputs e (machine child) -> StrictOrderReturn.result bias e child ret ->
 StrictOrderClear.result bias e ret q -> StrictCandidateInputs.data e caller q -> context bias parent e caller q.
Proof.
 intros F Out R C Inputs;pose proof(StrictOrderReturn.gprs _ _ _ _ R) as G;pose proof(StrictOrderClear.gprs _ _ _ _ C) as K.
 constructor.
 - eapply ScoreSaved.keep with (s:=machine child);[exact F|rewrite K,G by discriminate;reflexivity|].
   intros x X;rewrite (StrictOrderClear.memory _ _ _ _ C);apply (StrictOrderReturn.frame _ _ _ _ R).
   pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia));unfold ScoreSaved.area,StrictOrderReturn.region,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,Return.sp in *;lia.
 - unfold outputs in *;rewrite (K 13%nat),(K 14%nat),(K 15%nat),(G 13%nat),(G 14%nat),(G 15%nat) by discriminate;exact Out.
 - intro PC;pose proof(StrictOrderClear.pc _ _ _ _ C) as At;destruct (_=?0) in At;lia.
 - intro;exact Inputs.
Qed.
End Iteration.
