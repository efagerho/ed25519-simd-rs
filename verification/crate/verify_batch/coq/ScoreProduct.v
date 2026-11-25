From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require ScoreProgress StrictCandidateCall LadderTop.
Local Open Scope Z_scope.

Definition rejected pol screen:=match pol with Dalek=>regs(machine screen) 12%nat=?0 | Zip215=>false end.
Definition staging pol bias screen stop:=match pol with
 | Zip215=>stop=screen
 | Dalek=>exists candidate,StrictCandidateCall.execute bias screen=Some candidate /\
    ScoreProgress.product Dalek bias candidate stop end.
Definition observed pol bias screen stop:=exists staged seed,staging pol bias screen staged /\
 LadderSeed.execute bias staged=Some seed /\ LadderTop.execute bias seed=Some stop.
Definition selected pol bias e stop:=exists ladder staged seed,LadderStage.observed bias ladder staged /\
 LadderStage.selected ladder staged /\ LadderProduct.meaning pol bias e ladder /\
 LadderSeed.execute bias staged=Some seed /\ LadderSeed.seeded ladder staged seed /\ LadderSeed.odd_point e ladder seed /\
 LadderTop.result bias e ladder seed stop.

Lemma stage_checked pol bias pc e h r caller score screen :
 placement e -> loaded pol bias (mem e) (writable e) -> ProductRun.geometry (HashLayout.chunk pol e bias) ->
 HashLayout.active pol e -> ScoreStart.reached pol bias pc e h r caller score -> ScoreProgress.observed pol bias score screen ->
 rejected pol screen=false ->
 (exists staged,staging pol bias screen staged) /\
 (forall staged,staging pol bias screen staged -> exists mid ladder,
    LadderEntry.entry pol bias e mid ladder /\ LadderStage.observed bias ladder staged).
Proof.
 intros P I G Live Start Screen On.
 destruct pol.
 - split;[exists screen;reflexivity|intros stop ->].
   exact (proj2(ScoreProgress.zip _ _ _ _ _ _ _ P I G Start) _ Screen).
 - change ((regs(machine screen) 12%nat=?0)=false) in On;apply Z.eqb_neq in On.
   destruct(proj2(StrictScreen.with_frame _ _ _ _ _ _ _ P I Live Start) _ Screen) as [D F].
   destruct(StrictCandidateCall.checked _ _ _ _ _ _ _ P I (ScoreStart.caller _ _ _ _ _ _ _ _ Start) D F On)
      as [candidate [Call [E _]]].
   destruct(ScoreProgress.product_checked _ _ _ _ P I G E) as [[stop Product] Sound].
   split;[exists stop,candidate;auto|].
   intros q [p [Run Staged]];rewrite Call in Run;injection Run as <-.
   exact (Sound _ Staged).
Qed.

Theorem checked pol bias pc e h r caller score screen :
 placement e -> loaded pol bias (mem e) (writable e) -> ProductRun.geometry (HashLayout.chunk pol e bias) ->
 Tables.mapped e bias -> Candidate.constants e -> HashLayout.active pol e ->
 ScoreStart.reached pol bias pc e h r caller score -> ScoreProgress.observed pol bias score screen ->
 rejected pol screen=false ->
 (exists stop,observed pol bias screen stop) /\
 (forall stop,observed pol bias screen stop -> accounted e (writable e) stop /\ selected pol bias e stop).
Proof.
 intros P I G M Tables Live Start Screen On.
 destruct(stage_checked _ _ _ _ _ _ _ _ _ P I G Live Start Screen On) as [[staged Stage] Sound].
 split.
 - destruct(Sound _ Stage) as [mid [ladder [E End]]].
   destruct(LadderSeed.checked _ _ _ _ _ _ I G E End) as [seed [Run _]].
   destruct(LadderTop.checked _ _ _ _ _ _ _ I M Tables G E End Run) as [stop [Top _]].
   exists stop,staged,seed;auto.
 - intros stop [v [seed [S [Seed Top]]]];destruct(Sound _ S) as [mid [ladder [E End]]].
   destruct(LadderTop.checked _ _ _ _ _ _ _ I M Tables G E End Seed) as [q [Run [Paid Pair]]].
   rewrite Top in Run;injection Run as Eq;subst q.
   destruct(LadderSeed.checked _ _ _ _ _ _ I G E End) as [q [SR [_ [_ [Actual _]]]]];rewrite Seed in SR;injection SR as Eq;subst q.
   pose proof(proj2(proj2(proj2(LadderStage.checked _ _ _ _ _ I G E) _ End))) as Selected.
   split;[exact Paid|exists ladder,v,seed;split;[exact End|split;[exact Selected|]]].
   split;[eapply LadderProduct.checked;eassumption|split;[exact Seed|split;[exact Actual|split;[|exact Pair]]]].
   eapply LadderSeed.represents;eassumption.
Qed.
