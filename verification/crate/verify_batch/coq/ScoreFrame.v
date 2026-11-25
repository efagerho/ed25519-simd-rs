From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.ScalarWords execution.MappedFetch
 execution.WordBounds execution.InstructionRoute memory.WriteTrace memory.ByteMemory.
From Machine Require abi.FramePointer.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require ScoreCall.
Local Open Scope Z_scope.

Definition top e:=Rows.frame e-8.
Definition buffer e:=FramePointer.bottom (top e) 1280.
Definition enter pol bias:=segment (bias+ScoreSetup.callee pol) (ScoreSetup.code pol) 9.
Lemma image pol : linked (ScoreSetup.code pol) FramePointer.pushes /\ linked (ScoreSetup.code pol) (FramePointer.allocation 1280).
Proof. destruct pol;repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Record ready pol bias e p q:Prop:=Ready {
 pc:ip q=bias+ScoreSetup.callee pol+24; writes:accounted e (writable e) q; words:well_formed(machine q);
 stack:regs(machine q) 4%nat=buffer e; fp:regs(machine q) 5%nat=top e-8;
 gpr:forall r,r<>4%nat -> r<>5%nat -> regs(machine q) r=regs(machine p) r;
 saved:mem(machine q)=replay (mem(machine p)) (FramePointer.stores (bias+ScoreSetup.callee pol) (top e) (regs(machine p)));
 log_after:log q=log p++FramePointer.stores (bias+ScoreSetup.callee pol) (top e) (regs(machine p))
}.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem checked pol bias pc0 e h r p : placement e -> loaded pol bias (mem e) (writable e) -> ScoreCall.entered pol bias pc0 e h r p ->
 exists q,enter pol bias p=Some q /\ ready pol bias e p q.
Proof.
 intros P I A;destruct(image pol) as [Code Align];set (o:=bias+ScoreSetup.callee pol);set (t:=top e).
 destruct(stack_ok _ P) as [[L H] _];assert (Fit:1392<=t<2^64) by (unfold t,top,Rows.frame,sp in *;lia).
 pose proof(proj1(ScoreCall.args _ _ _ _ _ _ _ A)) as SP.
 destruct(FramePointer.save _ o (machine p) (carry p) t Code SP ltac:(lia)) as [a [R [AS [BP G]]]].
 destruct(FramePointer.allocate _ o a (carry p) t 1280 Align AS ltac:(lia) ltac:(lia)) as [b [c [B [S [M K]]]]].
 pose proof(run_append _ _ _ _ _ R _ _ _ B) as Run;rewrite app_nil_r in Run.
 pose proof(ScoreCall.writes _ _ _ _ _ _ _ A) as Acc.
 destruct(mapped_now _ _ _ I _ _ _ Acc (ScoreSetup.image pol)) as [Map Sep].
 assert (Safe:confined (writable e) (FramePointer.stores o t (regs(machine p)))).
 { eapply Forall_impl;[|apply FramePointer.confined];intros w F x X;left;specialize(F x X);unfold t,top,span,Rows.frame,sp in *;lia. }
 destruct(at_segment _ _ p o _ 9 0 _ _ Acc ltac:(rewrite Z.add_0_r;exact (ScoreCall.target _ _ _ _ _ _ _ A)) Map Sep Run Safe) as [Next Paid].
 eexists;split;[exact Next|constructor].
 - reflexivity.
 - exact Paid.
 - exact (segment_wf _ _ _ _ _ (ScoreCall.words _ _ _ _ _ _ _ A) Next).
 - exact S.
 - cbn [LinkedRun.finish machine cpu_state];rewrite K by discriminate;exact BP.
 - intros g RS RB;cbn [LinkedRun.finish machine cpu_state];rewrite K,G by assumption;reflexivity.
 - exact (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Run)).
 - reflexivity.
Qed.
End Iteration.
