From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds
 memory.FlatMemory memory.ByteMemory memory.WriteTrace.
From Machine Require abi.FramePointer.
From Ed25519Simd.VerifyBatch Require Import Policy Return.
From Ed25519Simd.VerifyBatch Require StrictOrderClear.
Local Open Scope Z_scope.

Record data e caller p:Prop:=Data {
 stack:regs(machine p) 4%nat=ScoreFrame.buffer e;
 point:regs(machine p) 3%nat=BatchDecode.point e true;
 slot:read_word(mem(machine p))(ScoreFrame.buffer e)=Rows.frame e+768;
 parent:preserved (CandidateEntry.retained e) (mem(machine caller)) (mem(machine p))
}.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Lemma at_start bias pc e h r caller score : placement e -> ScoreStart.reached Dalek bias pc e h r caller score ->
 data e caller score.
Proof.
 intros P Start;pose proof(CandidateEntry.unchanged _ _ _ _ _ _ _ _ P Start) as Parent.
 destruct Start as [C [f [_ [F [_ S]]]]];destruct(ScoreStart.arguments _ _ _ _ _ S) as [BX [_ [_ [_ [_ [_ [SP _]]]]]]].
 constructor;[exact SP| | |exact Parent].
 { rewrite BX,(ScoreFrame.gpr _ _ _ _ _ F) by discriminate;exact (proj1(proj2(proj2(ScoreCall.args _ _ _ _ _ _ _ C)))). }
 rewrite (ScoreStart.memory _ _ _ _ _ S);cbn [ScoreStart.event].
 rewrite (ScoreFrame.gpr _ _ _ _ _ F) by discriminate;rewrite (proj1(proj2(ScoreCall.args _ _ _ _ _ _ _ C))).
 apply write_read_word;destruct(stack_ok _ P) as [[L H] _];unfold word64,Rows.frame,sp in *;lia.
Qed.

Lemma after_screen bias pc e h r caller score y t child ret q : placement e ->
 ScoreStart.reached Dalek bias pc e h r caller score -> StrictRStart.reached bias e score y ->
 StrictRCanonical.result bias e y t -> StrictRCall.called e bias t child -> regs(machine child) 3%nat=regs(machine t) 3%nat ->
 StrictOrderReturn.result bias e child ret -> StrictOrderClear.result bias e ret q -> data e caller q.
Proof.
 intros P Start Y C [_ [_ [_ [_ [M _]]]]] BX R End;pose proof(at_start _ _ _ _ _ _ _ P Start) as Before.
 assert (Same:preserved (fun x=>CandidateEntry.retained e x \/ span (ScoreFrame.buffer e) 8 x)
      (mem(machine score)) (mem(machine q))).
 { intros x X;pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)).
   assert (Away:~(ScoreFrame.buffer e-32<=x<ScoreFrame.buffer e)) by
      (unfold CandidateEntry.retained,span,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia).
   rewrite (StrictOrderClear.memory _ _ _ _ End),(StrictOrderReturn.frame _ _ _ _ R)
       by (unfold StrictOrderReturn.region;lia).
   rewrite M;unfold commit;rewrite write_outside by (change (~(ScoreFrame.buffer e-8<=x<ScoreFrame.buffer e-8+8));lia).
   rewrite (StrictRCanonical.memory _ _ _ _ C),(StrictRStart.memory _ _ _ _ Y);reflexivity. }
 constructor.
 - rewrite (StrictOrderClear.gprs _ _ _ _ End) by discriminate;exact (StrictOrderReturn.rsp _ _ _ _ R).
 - rewrite (StrictOrderClear.gprs _ _ _ _ End),(StrictOrderReturn.gprs _ _ _ _ R) by discriminate;rewrite BX.
   exact (StrictRFrame.point _ _ _ _ _ (StrictRFrame.checked _ _ _ _ _ _ _ _ _ P Start Y C)).
 - rewrite <-(slot _ _ _ Before);apply preserved_read with (outside:=fun x=>CandidateEntry.retained e x \/ span (ScoreFrame.buffer e) 8 x);
   [exact Same|intros i B;right;change (0<=i<8) in B;unfold span;lia].
 - intros x X;rewrite Same by (left;exact X);apply (parent _ _ _ Before),X.
Qed.
End Iteration.
