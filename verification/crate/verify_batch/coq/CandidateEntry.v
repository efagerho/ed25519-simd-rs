From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Machine Require abi.FramePointer.
From Ed25519Simd.VerifyBatch Require Import Policy Return.
From Ed25519Simd.VerifyBatch Require ScoreStart.
Local Open Scope Z_scope.

Definition retained e x:=x<sp e-16384 \/ Rows.frame e<=x.
Lemma read_above e a m m' : preserved (retained e) m m' -> Rows.frame e<=a ->
 read_word m' a=read_word m a.
Proof.
 intros M A;apply preserved_read with (outside:=retained e);[exact M|].
 intros k K;right;change (0<=k<8) in K;lia.
Qed.

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
 ladder_ptrs:read_word (mem(machine p)) (Rows.frame e+832)=regs e 9%nat /\
   read_word (mem(machine p)) (Rows.frame e+840)=scratch e+512;
 digest_ptr:read_word (mem(machine p)) (Rows.frame e+848)=Rows.frame e;
 digest:forall j,(j<8)%nat -> HashLayout.eligible pol e j ->
  Scalar.ScalarSpec.lane_input (buffer_words (mem(machine p)) (Rows.frame e)) j=
  little_endian (SHA512.Spec.sha512 (r_bytes(HashLayout.row e j)++key_bytes(HashLayout.row e j)++message(HashLayout.row e j)));
 buffers:ScoreBuffers.data e (machine p)
}.
Lemma from_caller pol bias pc e h r caller q : placement e -> ScoreCall.entered pol bias pc e h r caller ->
 preserved (retained e) (mem(machine caller)) (mem(machine q)) ->
 ip q=bias+ScoreStart.candidate pol -> accounted e (writable e) q -> well_formed(machine q) ->
 regs(machine q) 4%nat=ScoreFrame.buffer e-8 -> regs(machine q) 7%nat=ScoreFrame.buffer e ->
 regs(machine q) 6%nat=Rows.frame e+768 -> entry pol bias e q.
Proof.
 intros P Entry M At Paid W SP DI SI;constructor;try assumption.
 - rewrite !(read_above _ _ _ _ M) by lia.
   destruct (ScoreCall.stack_args _ _ _ _ _ _ _ Entry) as [_ [Base [Sdigits _]]];auto.
 - rewrite (read_above _ _ _ _ M) by lia;exact (proj2(proj2(proj2(ScoreCall.stack_args _ _ _ _ _ _ _ Entry)))).
 - intros j J On;etransitivity;[|exact (ScoreCall.digest _ _ _ _ _ _ _ Entry j J On)].
   unfold Scalar.ScalarSpec.lane_input;f_equal;apply map_ext_in;intros k K;unfold buffer_words.
   apply preserved_read with (outside:=retained e);[exact M|intros n N;right;change (0<=n<8) in N;lia].
 - eapply ScoreBuffers.keep;[|exact (ScoreCall.buffers _ _ _ _ _ _ _ Entry)];intros x X;apply M.
   destruct(scratch_stack _ P);unfold ScoreBuffers.region,retained,span,Rows.frame,sp,disjoint in *;lia.
Qed.

Theorem zip bias pc e h r caller q : placement e -> ScoreStart.reached Zip215 bias pc e h r caller q -> entry Zip215 bias e q.
Proof.
 intros P Reached;pose proof(unchanged _ _ _ _ _ _ _ _ P Reached) as M;destruct Reached as [Entry [f [_ [F [_ S]]]]].
 destruct(ScoreStart.arguments _ _ _ _ _ S) as [_ [_ [_ [_ [_ [_ [SP [DI SI]]]]]]]].
 eapply from_caller;[exact P|exact Entry|exact M|exact (ScoreStart.pc _ _ _ _ _ S)|exact (ScoreStart.writes _ _ _ _ _ S)|
    exact (ScoreStart.words _ _ _ _ _ S)|exact SP|exact DI|].
 rewrite SI,(ScoreFrame.gpr _ _ _ _ _ F) by discriminate;exact (proj1(proj2(ScoreCall.args _ _ _ _ _ _ _ Entry))).
Qed.
