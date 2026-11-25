From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.WordBounds execution.WordSemantics
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute execution.RipBroadcasts abi.SysV
 memory.ByteMemory memory.WriteTrace memory.FlatMemory.
From Machine Require abi.FramePointer.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require StrictResume StrictMatchMath.
Import ListNotations. Local Open Scope Z_scope.
Local Notation pc:=(ScoreSetup.callee Dalek).
Local Notation text:=(ScoreSetup.code Dalek).
Definition flags e s:=forall j,(j<8)%nat -> let byte:=mem s (Rows.frame e+856+Z.of_nat j) in
 (byte=0 \/ byte=1) /\ (byte=1 <-> HashLayout.eligible Dalek e j).
Record context bias parent e caller s:Prop:=Context {
 rsp:regs s 4%nat=ScoreFrame.buffer e; r_ptr:regs s 3%nat=BatchDecode.point e true;
 product:regs s 7%nat=ScoreFrame.buffer e; args:StrictScoreFrame.outputs e s;
 saved:ScoreSaved.frame bias parent e caller s; eligibility:flags e s; operands:ScorePoint.points Dalek e s;
 constants:forall j,StrictMatchMath.constants (vectors s j)
}.
Definition private e x:=ScoreFrame.buffer e-16<=x<ScoreFrame.buffer e.
Definition kept r:=In r [3;4;5;7;13;14;15]%nat.

Lemma preserve bias parent e caller s t:placement e -> context bias parent e caller s ->
 (forall r,kept r -> regs t r=regs s r) -> preserved (fun x=>~private e x) (mem s) (mem t) ->
 (forall j,StrictMatchMath.constants (vectors t j)) -> context bias parent e caller t.
Proof.
 intros P [SP R Q Out Frame Flags Points _] G M Constants;pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)) as Gap.
 constructor.
 - rewrite G by (unfold kept;simpl;tauto);exact SP.
 - rewrite G by (unfold kept;simpl;tauto);exact R.
 - rewrite G by (unfold kept;simpl;tauto);exact Q.
 - unfold StrictScoreFrame.outputs;rewrite (G 13%nat),(G 14%nat),(G 15%nat) by (unfold kept;simpl;tauto);exact Out.
 - eapply ScoreSaved.keep;[exact Frame|apply G;unfold kept;simpl;tauto|].
   intros x X;apply M;unfold private,ScoreSaved.area,ScoreFrame.buffer,FramePointer.bottom in *;lia.
 - intros j J;cbv zeta;rewrite M;[exact(Flags j J)|unfold private,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top in *;lia].
 - eapply ScorePoint.keep_points;[|exact Points];intros x X;apply M;destruct(scratch_stack _ P);
   unfold FlatMemory.disjoint,private,span,BatchDecode.point,BatchDecode.point_offset,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia.
 - exact Constants.
Qed.

Definition literal:=DecoderFrame.helper+0xde0-pc.
Definition setup:=RipBroadcasts.route 4 196 28 literal.
Definition first:list line:=[(193,3%nat,CopyG 7 4)].
Lemma image:linked text first /\ linked text setup.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute bias:=segment (bias+pc) text 5.

Theorem checked bias parent e caller p:loaded Dalek bias (mem e) (writable e) -> StrictResume.result bias parent e caller p ->
 exists q,execute bias p=Some q /\ ip q=bias+pc+236 /\ accounted e (writable e) q /\ well_formed(machine q) /\
 context bias parent e caller (machine q) /\ regs(machine q) 12%nat=regs(machine p) 12%nat.
Proof.
 intros I Before;set(s:=machine p);set(o:=bias+pc);set(v:=set s 7 (regs s 4%nat)).
 assert (First:run 1 (ScalarBytes.fetch o text) (State(Running 193) s (carry p))=Some(State(Running 196) v (carry p),[])).
 { apply (InstructionRoute.checked _ _ _ (proj1 image));reflexivity. }
 destruct(RipBroadcasts.load o text 4 196 28 literal v (carry p) (proj2 image)) as [u [Load [G [M [_ [Const _]]]]]].
 pose proof(run_append _ _ _ _ _ First _ _ _ Load) as Run.
 pose proof(StrictResume.writes _ _ _ _ _ Before) as Prev;destruct(mapped_now _ _ _ I _ _ _ Prev (ScoreSetup.image Dalek)) as [Map Sep].
 destruct(at_segment _ _ p o text 5 _ _ _ Prev (StrictResume.pc_after _ _ _ _ _ Before) Map Sep Run (Forall_nil _)) as [Next Paid].
 eexists;split;[exact Next|split;[reflexivity|split;[exact Paid|split;[exact (segment_wf _ _ _ _ _ (StrictResume.words _ _ _ _ _ Before) Next)|]]]].
 change (context bias parent e caller u /\ regs u 12%nat=regs s 12%nat);split;[constructor|rewrite G;reflexivity].
 - rewrite G;exact(StrictResume.sp_after _ _ _ _ _ Before).
 - rewrite G;exact(StrictResume.r_ptr _ _ _ _ _ Before).
 - rewrite G;exact(StrictResume.sp_after _ _ _ _ _ Before).
 - unfold StrictScoreFrame.outputs;rewrite G;exact (StrictResume.outputs _ _ _ _ _ Before).
 - eapply ScoreSaved.keep;[exact (StrictResume.saved _ _ _ _ _ Before)|rewrite G;reflexivity|intros x X;rewrite M;reflexivity].
 - intros j J;cbv zeta;rewrite M;exact (StrictResume.flags _ _ _ _ _ Before j J).
 - apply (ScorePoint.keep_points Dalek e s u);[intros x X;rewrite M;reflexivity|exact (StrictResume.operands _ _ _ _ _ Before)].
 - intros j i K;rewrite Const by exact K.
   destruct(mapped_now _ _ _ I _ _ _ Prev (BatchDecode.helper_in Dalek)) as [Helper _].
   pose proof(proj1(symbols _ _ _ _ I _ _ (BatchDecode.helper_in Dalek))) as Bound.
   change (read_word (mem s) (word(o+literal+8*Z.of_nat i))=DecoderFrame.constant i).
   replace (o+literal+8*Z.of_nat i) with (bias+DecoderFrame.origin+DecoderFrame.at_literal i-DecoderFrame.origin)
     by (unfold o,literal,DecoderFrame.at_literal;ring).
   apply (DecoderFrame.mapped_value _ bias i K Helper).
   destruct Bound;pose proof(DecoderFrame.offsets _ K);unfold DecoderFrame.field_offset,DecoderFrame.at_literal,DecoderFrame.helper,word64 in *;lia.
Qed.
