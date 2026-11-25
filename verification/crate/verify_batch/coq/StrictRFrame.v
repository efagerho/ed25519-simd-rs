From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Machine Require abi.FramePointer.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require StrictRCanonical.
Local Open Scope Z_scope.

(* Live arguments on both sides of the canonicality branch. Each saved
   register word and the scorer return address come from actual stores. *)
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record inputs bias parent e child t:Prop:=Inputs {
 stack:regs(machine t) 4%nat=ScoreFrame.buffer e; fp:regs(machine t) 5%nat=ScoreFrame.top e-8;
 point:regs(machine t) 3%nat=BatchDecode.point e true;
 outputs:regs(machine t) 13%nat=Rows.frame e+856 /\ regs(machine t) 14%nat=output e /\ regs(machine t) 15%nat=regs e 6%nat;
 rows:PreparedInputs.signature e (machine t);
 caller_frame:preserved (fun x=>x<sp e-16384 \/ ScoreFrame.top e-48<=x)
   (replay (mem(machine child)) (FramePointer.stores (bias+ScoreSetup.callee Dalek) (ScoreFrame.top e) (regs(machine child))))
   (mem(machine t));
 return_word:read_word (mem(machine t)) (ScoreFrame.top e)=bias+parent+539
}.

Lemma checked bias parent e h r child score p t : placement e ->
 ScoreStart.reached Dalek bias parent e h r child score ->
 StrictRStart.reached bias e score p -> StrictRCanonical.result bias e p t -> inputs bias parent e child t.
Proof.
 intros P Start First Last.
 pose proof(CandidateEntry.unchanged _ _ _ _ _ _ _ _ P Start) as Kept.
 destruct Start as [Call [f [_ [F [_ S]]]]].
 destruct(ScoreStart.arguments _ _ _ _ _ S) as [BX [_ [R13 [R14 [R15 [BP [SP _]]]]]]].
 destruct(ScoreCall.args _ _ _ _ _ _ _ Call) as [_ [_ [R [DX [Flags [Out N]]]]]].
 assert (G:forall g,g<>0%nat -> g<>12%nat -> regs(machine t) g=regs(machine score) g).
 { intros g A B;rewrite (StrictRCanonical.unchanged_regs _ _ _ _ Last),(StrictRStart.unchanged_regs _ _ _ _ First) by assumption;reflexivity. }
 assert (Memory:mem(machine t)=mem(machine score)) by
   (rewrite (StrictRCanonical.memory _ _ _ _ Last);apply (StrictRStart.memory _ _ _ _ First)).
 assert (Saved:preserved (fun x=>x<sp e-16384 \/ ScoreFrame.top e-48<=x)
     (replay (mem(machine child)) (FramePointer.stores (bias+ScoreSetup.callee Dalek) (ScoreFrame.top e) (regs(machine child))))
     (mem(machine t))).
 { intros x X;rewrite Memory,(ScoreStart.memory _ _ _ _ _ S);unfold commit;rewrite write_outside.
   - rewrite (ScoreFrame.saved _ _ _ _ _ F);reflexivity.
   - change (~(ScoreFrame.buffer e<=x<ScoreFrame.buffer e+8)).
     pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia));unfold ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia. }
 constructor.
 - rewrite G by discriminate;exact SP.
 - rewrite G,BP by discriminate;exact (ScoreFrame.fp _ _ _ _ _ F).
 - rewrite G,BX,(ScoreFrame.gpr _ _ _ _ _ F) by discriminate;exact R.
 - rewrite (G 13%nat),(G 14%nat),(G 15%nat),R13,R14,R15 by discriminate.
   rewrite (ScoreFrame.gpr _ _ _ _ _ F 1),(ScoreFrame.gpr _ _ _ _ _ F 8),(ScoreFrame.gpr _ _ _ _ _ F 9) by discriminate;auto.
 - eapply DecodedRows.keep;[|exact (PreparedInputs.signature_point _ _ (ScoreBuffers.operands _ _ (ScoreCall.buffers _ _ _ _ _ _ _ Call)))].
   intros x X;rewrite Memory;apply Kept;destruct(scratch_stack _ P);unfold CandidateEntry.retained,span,BatchDecode.point,BatchDecode.point_offset,
    FlatMemory.disjoint,Rows.frame,sp in *;lia.
 - exact Saved.
 - rewrite <-(proj1(ScoreCall.stack_args _ _ _ _ _ _ _ Call)).
   apply preserved_read with (outside:=fun x=>ScoreFrame.top e<=x);[|intros off O;change (0<=off<8) in O;unfold ScoreFrame.top;lia].
   intros x X;rewrite Saved by lia;apply (WriteTrace.frame _ _ (FramePointer.confined _ _ _));lia.
Qed.
End Iteration.
