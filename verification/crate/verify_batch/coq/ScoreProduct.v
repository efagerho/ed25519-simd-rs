From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require ScoreProgress StrictCandidateCall.
Local Open Scope Z_scope.

Definition rejected pol screen:=match pol with Dalek=>regs(machine screen) 12%nat=?0 | Zip215=>false end.
Definition observed pol bias screen stop:=match pol with
 | Zip215=>stop=screen
 | Dalek=>exists candidate,StrictCandidateCall.execute bias screen=Some candidate /\
    ScoreProgress.product Dalek bias candidate stop end.
Definition selected pol bias e stop:=exists ladder,LadderStage.observed bias ladder stop /\
 LadderStage.selected ladder stop /\ LadderProduct.meaning pol bias e ladder.

Theorem checked pol bias pc e h r caller score screen :
 placement e -> loaded pol bias (mem e) (writable e) -> ProductRun.geometry (HashLayout.chunk pol e bias) ->
 Tables.mapped e bias -> Candidate.constants e -> HashLayout.active pol e ->
 ScoreStart.reached pol bias pc e h r caller score -> ScoreProgress.observed pol bias score screen ->
 rejected pol screen=false ->
 (exists stop,observed pol bias screen stop) /\
 (forall stop,observed pol bias screen stop -> accounted e (writable e) stop /\ selected pol bias e stop).
Proof.
 intros P I G M Tables Live Start Screen On.
 assert (Finish:forall stop mid ladder,LadderEntry.entry pol bias e mid ladder -> LadderStage.observed bias ladder stop ->
      accounted e (writable e) stop /\ selected pol bias e stop).
 { intros stop mid ladder E End;destruct(proj2(LadderStage.checked _ _ _ _ _ I G E) _ End) as [Paid [_ Rows]].
   split;[exact Paid|exists ladder;split;[exact End|split;[exact Rows|]]].
   eapply LadderProduct.checked;[exact I|exact M|exact Tables|exact G|exact E]. }
 destruct pol.
 - split;[exists screen;reflexivity|intros stop ->].
   destruct(proj2(ScoreProgress.zip _ _ _ _ _ _ _ P I G Start) _ Screen) as [mid [ladder [E End]]].
   exact (Finish _ _ _ E End).
 - change ((regs(machine screen) 12%nat=?0)=false) in On;apply Z.eqb_neq in On.
   destruct(proj2(StrictScreen.with_frame _ _ _ _ _ _ _ P I Live Start) _ Screen) as [D F].
   destruct(StrictCandidateCall.checked _ _ _ _ _ _ _ P I (ScoreStart.caller _ _ _ _ _ _ _ _ Start) D F On)
      as [candidate [Call [E _]]].
   destruct(ScoreProgress.product_checked _ _ _ _ P I G E) as [[stop Product] Sound].
   split;[exists stop,candidate;auto|].
   intros q [p [Run Staged]];rewrite Call in Run;injection Run as <-.
   destruct(Sound _ Staged) as [mid [ladder [Entry End]]];exact (Finish _ _ _ Entry End).
Qed.
