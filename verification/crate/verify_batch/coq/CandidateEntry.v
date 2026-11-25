From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Machine Require abi.FramePointer.
From Ed25519Simd.VerifyBatch Require Import Policy Return.
From Ed25519Simd.VerifyBatch Require ScoreStart.
Local Open Scope Z_scope.

Definition retained e x:=x<sp e-16384 \/ Rows.frame e<=x.
Lemma unchanged pol bias pc e h r caller q : placement e -> ScoreStart.reached pol bias pc e h r caller q ->
 preserved (retained e) (mem(machine caller)) (mem(machine q)).
Proof.
 intros P [_ [f [_ [F [_ S]]]]] x X;rewrite (ScoreStart.memory _ _ _ _ _ S),(ScoreFrame.saved _ _ _ _ _ F).
 pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)) as Gap.
 assert (Outside:~WriteTrace.touches (ScoreStart.event pol bias (ScoreFrame.buffer e) (regs(machine f) 7%nat)) x).
 { unfold touches;destruct pol;cbn [ScoreStart.event qword address size];change (Z.of_nat 8) with 8;
   unfold retained,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia. }
 unfold commit;rewrite write_outside by exact Outside;apply (WriteTrace.frame _ _
  (FramePointer.confined (bias+ScoreSetup.callee pol) (ScoreFrame.top e) (regs(machine caller))));unfold retained,ScoreFrame.top,Rows.frame,sp in *;lia.
Qed.

Record entry pol bias e p:Prop:=Entry {
 at_call:ip p=bias+ScoreStart.candidate pol; writes:accounted e (writable e) p; words:well_formed(machine p);
 stack:regs(machine p) 4%nat=ScoreFrame.buffer e-8;
 point:regs(machine p) 7%nat=ScoreFrame.buffer e;
 inputs:regs(machine p) 6%nat=Rows.frame e+768;
 digest_ptr:read_word (mem(machine p)) (Rows.frame e+848)=Rows.frame e;
 digest:forall j,(j<8)%nat -> HashLayout.eligible pol e j ->
  Scalar.ScalarSpec.lane_input (buffer_words (mem(machine p)) (Rows.frame e)) j=
  little_endian (SHA512.Spec.sha512 (r_bytes(HashLayout.row e j)++key_bytes(HashLayout.row e j)++message(HashLayout.row e j)));
 buffers:ScoreBuffers.data e (machine p)
}.
Theorem zip bias pc e h r caller q : placement e -> ScoreStart.reached Zip215 bias pc e h r caller q -> entry Zip215 bias e q.
Proof.
 intros P Reached;pose proof(unchanged _ _ _ _ _ _ _ _ P Reached) as M;destruct Reached as [Entry [f [_ [F [_ S]]]]].
 destruct(ScoreStart.arguments _ _ _ _ _ S) as [_ [_ [_ [_ [_ [_ [SP [DI SI]]]]]]]].
 constructor;[exact (ScoreStart.pc _ _ _ _ _ S)|exact (ScoreStart.writes _ _ _ _ _ S)|exact (ScoreStart.words _ _ _ _ _ S)|exact SP|exact DI| | | |].
 - rewrite SI,(ScoreFrame.gpr _ _ _ _ _ F) by discriminate;exact (proj1(proj2(ScoreCall.args _ _ _ _ _ _ _ Entry))).
 - etransitivity;[|exact (proj2(proj2(proj2(ScoreCall.stack_args _ _ _ _ _ _ _ Entry))))].
   apply preserved_read with (outside:=retained e);[exact M|intros k K;right;change (0<=k<8) in K;lia].
 - intros j J On;etransitivity;[|exact (ScoreCall.digest _ _ _ _ _ _ _ Entry j J On)].
   unfold Scalar.ScalarSpec.lane_input;f_equal;apply map_ext_in;intros k K;unfold buffer_words.
   apply preserved_read with (outside:=retained e);[exact M|intros n N;right;change (0<=n<8) in N;lia].
 - eapply ScoreBuffers.keep;[|exact (ScoreCall.buffers _ _ _ _ _ _ _ Entry)];intros x X;apply M.
   destruct(scratch_stack _ P);unfold ScoreBuffers.region,retained,span,Rows.frame,sp,disjoint in *;lia.
Qed.
