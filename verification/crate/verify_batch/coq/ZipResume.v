From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds abi.SysV
 memory.FlatMemory memory.ByteMemory memory.WriteTrace.
From Machine Require abi.FramePointer.
From Curve25519.group Require Import Affine Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require ScoreProduct.
Local Open Scope Z_scope.

Definition product e j A:=let i:=HashLayout.row e j in
 plus (scale (little_endian(s_bytes i)) generator) (scale (-challenge i) A).
Definition accumulator e s:=buffer_words (mem s) (ScoreFrame.buffer e).
Record points e s:Prop:=Points {
 reduced:strict (accumulator e s);
 value:forall j A,(j<8)%nat -> HashLayout.eligible Zip215 e j ->
   decodes (little_endian(key_bytes(HashLayout.row e j))) A ->
   represents_point true (point_values (accumulator e s) j) (product e j A);
 signature:PreparedInputs.signature e s
}.
Definition live e s:=forall j,(j<8)%nat ->
 Z.testbit (regs s 12%nat) (Z.of_nat j)=true <-> RootDecision.decodes true e j.
Definition flags e s:=forall j,(j<8)%nat -> let byte:=mem s (Rows.frame e+856+Z.of_nat j) in
 (byte=0 \/ byte=1) /\ (byte=1 <-> HashLayout.eligible Zip215 e j).
Record ready bias pc e caller q:Prop:=Ready {
 at_return:ip q=ScoreProduct.continuation Zip215 bias;
 words:well_formed(machine q); writes:accounted e (writable e) q;
 stack:regs(machine q) 4%nat=ScoreFrame.buffer e;
 decoded:regs(machine q) 3%nat=BatchDecode.point e true;
 mask:live e (machine q); outputs:StrictScoreFrame.outputs e (machine q);
 frame:ScoreSaved.frame bias pc e caller (machine q);
 eligibility:flags e (machine q); operands:points e (machine q)
}.

Theorem checked bias pc e h r caller score q:placement e ->
 ScoreStart.reached Zip215 bias pc e h r caller score ->
 ip q=ScoreProduct.continuation Zip215 bias -> CandidateEntry.entry Zip215 bias e score ->
 ScoreProduct.from_candidate Zip215 bias e score q -> ready bias pc e caller q.
Proof.
 intros P [C [f [_ [F [_ S]]]]] PC Entry [prev [ladder [u [_ [Prod [Ret Mem]]]]]].
 pose proof(ScoreFrame.gpr _ _ _ _ _ F) as Keep;pose proof(CandidateReturn.saved _ _ _ Ret) as Restore.
 destruct(ScoreStart.arguments _ _ _ _ _ S) as [BX [Mask [R13 [R14 [R15 [BP _]]]]]].
 destruct(ScoreCall.args _ _ _ _ _ _ _ C) as [_ [_ [Ptr [DX [CX [R8 R9]]]]]].
 pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)) as Pad.
 assert (Above:forall x,ScoreSaved.area e x -> CandidateFrame.outside e x).
 { unfold ScoreSaved.area,CandidateFrame.outside,ScoreFrame.buffer,FramePointer.bottom;lia. }
 constructor.
 - exact PC.
 - exact (CandidateReturn.words _ _ _ Ret).
 - exact (CandidateReturn.log_ok _ _ _ Ret).
 - exact (CandidateReturn.stack _ _ _ Ret).
 - rewrite Restore,BX,Keep by (simpl;tauto || discriminate);exact Ptr.
 - intros j J;rewrite Restore,Mask,Keep by (simpl;tauto || discriminate).
   rewrite Z.mod_pow2_bits_low with (n:=8) by lia;apply (ScoreCall.validity _ _ _ _ _ _ _ C),J.
 - unfold StrictScoreFrame.outputs;rewrite (Restore 13%nat),(Restore 14%nat),(Restore 15%nat) by (simpl;tauto).
   now rewrite R13,R14,R15,!Keep by discriminate.
 - apply (ScoreSaved.from_call _ _ _ _ _ _ _ _ C).
   + rewrite Restore,BP by (simpl;tauto);exact (ScoreFrame.fp _ _ _ _ _ F).
   + intros x X;rewrite (CandidateReturn.parent _ _ _ Ret x (Above x X)),(ScoreStart.memory _ _ _ _ _ S).
     unfold commit;rewrite write_outside;[now rewrite (ScoreFrame.saved _ _ _ _ _ F)|].
     change (~(ScoreFrame.buffer e-8<=x<ScoreFrame.buffer e-8+8));unfold ScoreSaved.area,ScoreFrame.buffer,FramePointer.bottom in *;lia.
 - intros j J;cbv zeta;rewrite (CandidateReturn.parent _ _ _ Ret) by (apply Above;unfold ScoreSaved.area,ScoreFrame.top;lia).
   rewrite (ScoreStart.memory _ _ _ _ _ S);unfold commit;rewrite write_outside.
   + rewrite (ScoreFrame.saved _ _ _ _ _ F),(WriteTrace.frame _ _ (FramePointer.confined _ _ _)) by (unfold ScoreFrame.top;lia).
     apply (ScoreCall.lanes _ _ _ _ _ _ _ C),J.
   + change (~(ScoreFrame.buffer e-8<=Rows.frame e+856+Z.of_nat j<ScoreFrame.buffer e-8+8)).
     unfold ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top in *;lia.
 - constructor.
   + unfold accumulator;rewrite Mem;exact (LadderProduct.bound _ _ _ _ _ Prod).
   + unfold accumulator;rewrite Mem;exact (LadderProduct.value _ _ _ _ _ Prod).
   + eapply DecodedRows.keep;[|exact (PreparedInputs.signature_point _ _
       (ScoreBuffers.operands _ _ (CandidateEntry.buffers _ _ _ _ Entry)))].
     intros x X;apply (CandidateReturn.parent _ _ _ Ret);destruct(scratch_stack _ P);
     unfold CandidateFrame.outside,CandidateDigest.dst,CandidateDigest.top,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp,
       BatchDecode.point,BatchDecode.point_offset,FlatMemory.disjoint,span in *;lia.
Qed.

Lemma keep_points e s t : preserved (fun x=>span (ScoreFrame.buffer e) 1280 x \/ span (BatchDecode.point e true) 1280 x)
 (mem s) (mem t) -> points e s -> points e t.
Proof.
 intros Keep [Bounds Group Sig].
 assert (E:forall k,(k<160)%nat -> accumulator e t k=accumulator e s k).
 { intros k K;apply preserved_read with (outside:=span (ScoreFrame.buffer e) 1280).
   - intros x X;apply Keep;left;exact X.
   - intros i I;change (0<=i<8) in I;unfold span;lia. }
 constructor.
 - intros c j C J i I;unfold cell;rewrite E by lia;apply Bounds;assumption.
 - intros j A J On K;rewrite (point_values_ext _ _ _ E J);apply Group;assumption.
 - eapply DecodedRows.keep;[|exact Sig];intros x X;apply Keep;right;exact X.
Qed.
