From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.ScalarWords execution.MappedFetch.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require StrictScreen ScoreTail.
Local Open Scope Z_scope.
Local Notation pc:=(ScoreSetup.callee Dalek).
Local Notation text:=(ScoreSetup.code Dalek).

Definition prepare bias p:=if ip p=?bias+pc+565 then Some p else segment (bias+pc) text 4 p.
Definition execute bias p:=bind (prepare bias p) (ScoreTail.execute Dalek bias).

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem checked bias parent e caller p :
 placement e -> loaded Dalek bias (mem e) (writable e) ->
 StrictScreen.decision bias e p -> StrictScoreFrame.context bias parent e caller p ->
 regs(machine p) 12%nat=0 ->
 exists q,execute bias p=Some q /\
 exists t,prepare bias p=Some t /\ ScoreTail.entry bias parent e t q 0.
Proof.
 intros P I D F Zero;set (o:=bias+pc) in *.
 pose proof(StrictScreen.writes _ _ _ D) as Paid;pose proof(StrictScreen.words _ _ _ D) as W.
 pose proof(StrictScoreFrame.frame _ _ _ _ _ F) as Saved.
 assert (Ready:exists t,prepare bias p=Some t /\ ip t=o+565 /\ accounted e (writable e) t /\
      well_formed(machine t) /\ ScoreSaved.frame bias parent e caller (machine t) /\ ScoreTail.arguments e 0 (machine t)).
 { unfold prepare;fold o;destruct(Z.eqb_spec (ip p) (o+565)) as [At|Else].
   - exists p;split;[reflexivity|split;[exact At|split;[exact Paid|split;[exact W|split;[exact Saved|]]]]].
     exact (StrictScoreFrame.at_tail _ _ _ _ _ F At).
   - pose proof(StrictScreen.address _ _ _ D) as At;rewrite Zero in At;destruct At as [Bad|At];[contradiction|].
     destruct(StrictRCall.zero_raw o (machine p) (carry p)) as [u [Run [_ [AX [DI [SI [DX [BP M]]]]]]]].
     destruct(mapped_now _ _ _ I _ _ _ Paid (ScoreSetup.image Dalek)) as [Map Sep].
     destruct(at_segment _ _ p o _ 4 554 _ _ Paid At Map Sep Run (Forall_nil _)) as [End A].
     eexists;split;[exact End|split;[reflexivity|split;[exact A|split;[exact(segment_wf _ _ _ _ _ W End)|split]]]].
     + eapply ScoreSaved.keep;[exact Saved|exact BP|intros x X;change (mem u x=mem(machine p) x);now rewrite M].
     + change (ScoreTail.arguments e 0 u);unfold ScoreTail.arguments;rewrite AX,DI,SI,DX.
       split;[reflexivity|exact (StrictScoreFrame.arguments _ _ _ _ _ F)]. }
 destruct Ready as [t [Prepare [At [A [Words [Frame Args]]]]]].
 destruct(ScoreTail.checked Dalek bias parent e caller t 0 P I At A Words Frame Args) as [q [Tail Post]].
 exists q;split;[unfold execute;rewrite Prepare;exact Tail|exists t;auto].
Qed.
End Iteration.
