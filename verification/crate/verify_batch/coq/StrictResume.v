From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun abi.SysV memory.FlatMemory memory.ByteMemory.
From Machine Require abi.FramePointer.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require ScorePoint.
Local Open Scope Z_scope.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record result bias pc e caller q:Prop:=Result {
 pc_after:ip q=ScoreProduct.continuation Dalek bias; words:well_formed(machine q); writes:accounted e (writable e) q;
 sp_after:regs(machine q) 4%nat=ScoreFrame.buffer e; r_ptr:regs(machine q) 3%nat=BatchDecode.point e true;
 live:forall j,(j<8)%nat -> (Z.testbit (regs(machine q) 12%nat) (Z.of_nat j)=true <-> StrictOrderClear.eligible e j);
 outputs:StrictScoreFrame.outputs e (machine q); saved:ScoreSaved.frame bias pc e caller (machine q);
 flags:forall j,(j<8)%nat -> let byte:=mem(machine q)(Rows.frame e+856+Z.of_nat j) in
      (byte=0 \/ byte=1) /\ (byte=1 <-> HashLayout.eligible Dalek e j);
 operands:ScorePoint.points Dalek e (machine q)
}.

Theorem checked bias pc e h r caller screen candidate q : placement e -> loaded Dalek bias (mem e) (writable e) ->
 ScoreCall.entered Dalek bias pc e h r caller -> StrictScreen.decision bias e screen -> StrictScoreFrame.context bias pc e caller screen ->
 regs(machine screen) 12%nat<>0 -> StrictCandidateCall.execute bias screen=Some candidate ->
 ip q=ScoreProduct.continuation Dalek bias -> ScoreProduct.from_candidate Dalek bias e candidate q -> result bias pc e caller q.
Proof.
 intros P I C D F Live Run PC [prev [ladder [u [_ [Prod [Ret Mem]]]]]].
 destruct(StrictCandidateCall.checked _ _ _ _ _ _ _ P I C D F Live) as [v [Call [Entry [_ [_ [Regs Same]]]]]].
 rewrite Run in Call;injection Call as Eq;subst v.
 pose proof(StrictScoreFrame.candidate _ _ _ _ _ F Live) as Args.
 pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)) as Gap.
 assert (Area:forall x,ScoreSaved.area e x -> CandidateFrame.outside e x /\ ~(ScoreFrame.buffer e-8<=x<ScoreFrame.buffer e)).
 { unfold ScoreSaved.area,CandidateFrame.outside,ScoreFrame.buffer,FramePointer.bottom;lia. }
 assert (Keep:forall g,In g sysv_saved -> regs(machine q) g=regs(machine screen) g).
 { intros g G;now rewrite (CandidateReturn.saved _ _ _ Ret g G),(Regs g G). }
 assert (Parent:preserved (ScoreSaved.area e) (mem(machine screen)) (mem(machine q))).
 { intros x X;destruct(Area x X) as [A B];rewrite (CandidateReturn.parent _ _ _ Ret x A);apply Same,B. }
 constructor.
 - exact PC.
 - exact (CandidateReturn.words _ _ _ Ret).
 - exact (CandidateReturn.log_ok _ _ _ Ret).
 - exact (CandidateReturn.stack _ _ _ Ret).
 - rewrite Keep by (simpl;tauto);exact (StrictCandidateInputs.point _ _ _ Args).
 - intros j J;rewrite Keep by (simpl;tauto);exact (StrictScreen.lane _ _ _ D j J).
 - exact (StrictScoreFrame.keep_outputs _ _ _ (StrictScoreFrame.arguments _ _ _ _ _ F) Keep).
 - eapply ScoreSaved.keep;[exact (StrictScoreFrame.frame _ _ _ _ _ F)|apply Keep;simpl;tauto|exact Parent].
 - intros j J;cbv zeta;rewrite Parent by (unfold ScoreSaved.area,ScoreFrame.top;lia).
   rewrite (StrictCandidateInputs.parent _ _ _ Args) by (right;lia);apply (ScoreCall.lanes _ _ _ _ _ _ _ C),J.
 - exact (ScorePoint.returned _ _ _ _ _ _ _ P Entry Prod Ret Mem).
Qed.
End Iteration.
