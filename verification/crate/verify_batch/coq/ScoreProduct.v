From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds memory.ByteMemory memory.MemoryGeometry.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require CandidateReturn ScoreProgress StrictCandidateCall LadderTop.
Local Open Scope Z_scope.

Definition rejected pol screen:=match pol with Dalek=>regs(machine screen) 12%nat=?0 | Zip215=>false end.
Definition staging pol bias screen stop:=match pol with
 | Zip215=>stop=screen
 | Dalek=>exists candidate,StrictCandidateCall.execute bias screen=Some candidate /\
    ScoreProgress.product Dalek bias candidate stop end.
Definition observed pol bias screen stop:=exists staged seed high product,staging pol bias screen staged /\
 LadderSeed.execute bias staged=Some seed /\ LadderTop.execute bias seed=Some high /\
 LadderProduct.execute bias high=Some product /\ CandidateReturn.execute pol bias product=Some stop.
Definition continuation pol bias:=bias+ScoreSetup.callee pol+match pol with Zip215=>51|Dalek=>193 end.
Definition origin pol bias score screen candidate:=match pol with
 | Zip215=>candidate=score | Dalek=>StrictCandidateCall.execute bias screen=Some candidate end.
Definition from_candidate pol bias e candidate stop:=exists prev ladder product,
 LadderEntry.entry pol bias e prev ladder /\ LadderProduct.meaning pol bias e ladder product /\
 CandidateReturn.result e candidate stop /\ mem(machine stop)=mem(machine product).

Definition selected pol bias e stop:=ip stop=continuation pol bias /\ exists candidate,
 CandidateEntry.entry pol bias e candidate /\ from_candidate pol bias e candidate stop.

Lemma stage_checked pol bias pc e h r caller score screen :
 placement e -> loaded pol bias (mem e) (writable e) -> ProductRun.geometry (HashLayout.chunk pol e bias) ->
 HashLayout.active pol e -> ScoreStart.reached pol bias pc e h r caller score -> ScoreProgress.observed pol bias score screen ->
 rejected pol screen=false ->
 (exists staged,staging pol bias screen staged) /\
 (forall staged,staging pol bias screen staged -> exists candidate, origin pol bias score screen candidate /\ CandidateEntry.entry pol bias e candidate /\
    read_word (mem(machine candidate)) (CandidateDigest.top e)=continuation pol bias /\ ScoreProgress.context pol bias e candidate staged).
Proof.
 intros P I G Live Start Screen On.
 destruct pol.
 - split;[exists screen;reflexivity|intros stop ->].
   exists score;split;[reflexivity|split];[eapply CandidateEntry.zip;eassumption|split;[|exact (proj2(ScoreProgress.zip _ _ _ _ _ _ _ P I G Start) _ Screen)]].
   destruct Start as [_ [f [_ [_ [_ St]]]]];rewrite (ScoreStart.memory _ _ _ _ _ St).
   apply write_read_word;destruct(proj1(symbols _ _ _ _ I _ _ (ScoreSetup.image Zip215))) as [Lo Hi].
   assert (Size:51<Z.of_nat(length(ScoreSetup.code Zip215))) by (vm_compute;reflexivity);change (word64 (bias+ScoreSetup.callee Zip215+51));unfold word64;lia.
 - change ((regs(machine screen) 12%nat=?0)=false) in On;apply Z.eqb_neq in On.
   destruct(proj2(StrictScreen.with_frame _ _ _ _ _ _ _ P I Live Start) _ Screen) as [D F].
   destruct(StrictCandidateCall.checked _ _ _ _ _ _ _ P I (ScoreStart.caller _ _ _ _ _ _ _ _ Start) D F On)
      as [candidate [Call [E [_ Link]]]].
   destruct(ScoreProgress.product_checked _ _ _ _ P I G E) as [[stop Product] Sound].
   split;[exists stop,candidate;auto|].
   intros q [p [Run Staged]];rewrite Call in Run;injection Run as <-.
   exists candidate;split;[exact Call|split];[exact E|split;[exact Link|exact (Sound _ Staged)]].
Qed.

Theorem with_origin pol bias pc e h r caller score screen :
 placement e -> loaded pol bias (mem e) (writable e) -> ProductRun.geometry (HashLayout.chunk pol e bias) ->
 Tables.mapped e bias -> Candidate.constants e -> HashLayout.active pol e ->
 ScoreStart.reached pol bias pc e h r caller score -> ScoreProgress.observed pol bias score screen ->
 rejected pol screen=false ->
 (exists stop,observed pol bias screen stop) /\
 (forall stop,observed pol bias screen stop -> accounted e (writable e) stop /\ ip stop=continuation pol bias /\ exists candidate,
   origin pol bias score screen candidate /\ CandidateEntry.entry pol bias e candidate /\ from_candidate pol bias e candidate stop).
Proof.
 intros P I G M Tables Live Start Screen On.
 destruct(stage_checked _ _ _ _ _ _ _ _ _ P I G Live Start Screen On) as [[staged Stage] Sound].
 split.
 - destruct(Sound _ Stage) as [cand [At [Entry [Link [d [mid [ladder [D [RR [E End]]]]]]]]]].
   destruct(LadderSeed.checked _ _ _ _ _ _ I G E End) as [seed [Run _]].
   destruct(LadderTop.checked _ _ _ _ _ _ _ I M Tables G E End Run) as [top [High _]].
   destruct(LadderProduct.checked _ _ _ _ _ _ _ _ I M Tables G E End Run High) as [q [Ret [Paid Product]]].
   destruct(CandidateReturn.checked _ _ _ _ _ _ _ _ P I Entry D RR E Product Paid) as [stop [Finish _]].
   exists stop,staged,seed,top,q;auto.
 - intros stop [v [seed [top [q [Observed [Seed [High [Ret Finish]]]]]]]].
   destruct(Sound _ Observed) as [cand [At [Entry [Link [d [mid [ladder [D [RR [E End]]]]]]]]]].
   destruct(LadderProduct.checked _ _ _ _ _ _ _ _ I M Tables G E End Seed High) as [u [R [Paid Product]]].
   rewrite Ret in R;injection R as Eq;subst u.
   destruct(CandidateReturn.checked _ _ _ _ _ _ _ _ P I Entry D RR E Product Paid) as [u [R [Done Mem]]].
   rewrite Finish in R;injection R as Eq;subst u;split;[exact (CandidateReturn.log_ok _ _ _ Done)|].
   split;[now rewrite (CandidateReturn.back _ _ _ Done),Link|exists cand;split;[exact At|split;[exact Entry|exists mid,ladder,q;auto]]].
Qed.

Theorem checked pol bias pc e h r caller score screen :
 placement e -> loaded pol bias (mem e) (writable e) -> ProductRun.geometry (HashLayout.chunk pol e bias) ->
 Tables.mapped e bias -> Candidate.constants e -> HashLayout.active pol e ->
 ScoreStart.reached pol bias pc e h r caller score -> ScoreProgress.observed pol bias score screen ->
 rejected pol screen=false ->
 (exists stop,observed pol bias screen stop) /\
 (forall stop,observed pol bias screen stop -> accounted e (writable e) stop /\ selected pol bias e stop).
Proof.
 intros P I G M T On A B C;destruct(with_origin _ _ _ _ _ _ _ _ _ P I G M T On A B C) as [Ex All].
 split;[exact Ex|intros stop Run;destruct(All _ Run) as [Paid [PC [cand [_ Post]]]]].
 split;[exact Paid|split;[exact PC|now exists cand]].
Qed.
