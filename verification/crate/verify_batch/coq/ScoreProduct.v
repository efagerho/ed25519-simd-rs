From Coq Require Import ZArith Lia.
From Machine Require execution.Composition.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds memory.ByteMemory memory.MemoryGeometry.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require CandidateReturn ScoreProgress StrictCandidateCall LadderTop.
Local Open Scope Z_scope.

Definition rejected pol screen:=match pol with Dalek=>regs(machine screen) 12%nat=?0 | Zip215=>false end.
Definition staging pol bias screen stop:=match pol with
 | Zip215=>stop=screen
 | Dalek=>exists candidate,StrictCandidateCall.execute bias screen=Some candidate /\
    ScoreProgress.product Dalek bias candidate stop end.
Definition observed pol bias screen :=
 Composition.followed_by (staging pol bias screen) (fun staged =>
 Composition.followed_by (Composition.output (LadderSeed.execute bias staged)) (fun seed =>
 Composition.followed_by (Composition.output (LadderTop.execute bias seed)) (fun high =>
 Composition.followed_by (Composition.output (LadderProduct.execute bias high))
   (fun product => Composition.output (CandidateReturn.execute pol bias product))))).
Definition continuation pol bias:=bias+ScoreSetup.callee pol+match pol with Zip215=>51|Dalek=>193 end.
Definition origin pol bias score screen candidate:=match pol with
 | Zip215=>candidate=score | Dalek=>StrictCandidateCall.execute bias screen=Some candidate end.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
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
      as [candidate [Call [E [_ [Link _]]]]].
   apply (Composition.after_some Call). eapply Composition.consequence.
   + exact (ScoreProgress.product_checked _ _ _ _ P I G E).
   + intros stop _ Context. exists candidate; auto.
Qed.

Theorem with_origin pol bias pc e h r caller score screen :
 placement e -> loaded pol bias (mem e) (writable e) -> ProductRun.geometry (HashLayout.chunk pol e bias) ->
 Tables.mapped e bias -> Candidate.constants e -> HashLayout.active pol e ->
 ScoreStart.reached pol bias pc e h r caller score -> ScoreProgress.observed pol bias score screen ->
 rejected pol screen=false ->
 Composition.ensures (observed pol bias screen) (fun stop =>
   accounted e (writable e) stop /\ ip stop=continuation pol bias /\ exists candidate,
   origin pol bias score screen candidate /\ CandidateEntry.entry pol bias e candidate /\ from_candidate pol bias e candidate stop).
Proof.
 intros P I G M Tables Live Start Screen On.
 unfold observed. eapply Composition.sequence.
 - exact (stage_checked _ _ _ _ _ _ _ _ _ P I G Live Start Screen On).
 - intros staged [cand [At [Entry [Link [d [mid [ladder [D [RR [E End]]]]]]]]]].
   pose proof (LadderTables.supplied _ _ _ _ _ I M Tables E) as ValidTables.
   destruct (LadderSeed.checked _ _ _ _ _ _ I E End) as [seed [Seed Seeded]]. apply (Composition.after_some Seed).
   destruct (LadderTop.checked _ _ _ _ _ _ _ I ValidTables E End Seeded) as [top [High Pair]]. apply (Composition.after_some High).
   destruct (LadderProduct.checked _ _ _ _ _ _ _ _ I ValidTables E End Seeded Pair) as [q [Ret [Paid Product]]].
   apply (Composition.after_some Ret), Composition.option_result.
   destruct (CandidateReturn.checked _ _ _ _ _ _ _ _ P I Entry D RR E Product Paid) as [stop [Finish [Done Mem]]].
   exists stop; split; [exact Finish|split; [exact (CandidateReturn.log_ok _ _ _ Done)|]].
   split; [now rewrite (CandidateReturn.back _ _ _ Done),Link|].
   exists cand; split; [exact At|split; [exact Entry|exists mid,ladder,q; auto]].
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
End Iteration.
