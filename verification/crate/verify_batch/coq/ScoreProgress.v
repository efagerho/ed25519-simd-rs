From Coq Require Import ZArith.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require LadderProduct LadderStage StrictScreen.

(* The two scorers diverge after their common frame allocation. ZIP calls
   the candidate immediately. Dalek starts by screening its decoded R. *)
Definition product pol bias candidate stop := exists q mid ladder,
 CandidateDigest.enter pol bias candidate=Some q /\ ReducedDigest.observed bias q mid /\
 LadderEntry.enter pol bias mid=Some ladder /\ LadderStage.observed bias ladder stop.

Definition observed pol bias score stop : Prop := match pol with
 | Zip215=>product Zip215 bias score stop | Dalek=>StrictScreen.observed bias score stop end.

Theorem product_checked pol bias e candidate :
 placement e -> loaded pol bias (mem e) (writable e) -> ProductRun.geometry (HashLayout.chunk pol e bias) ->
 CandidateEntry.entry pol bias e candidate ->
 (exists stop,product pol bias candidate stop) /\
 (forall stop,product pol bias candidate stop -> exists mid ladder,LadderEntry.entry pol bias e mid ladder /\ LadderStage.observed bias ladder stop).
Proof.
 intros P I Geo C.
 destruct(CandidateDigest.checked _ _ _ _ P I C) as [q [Call Entry]].
 destruct(ReducedDigest.checked _ _ _ _ _ P I C Entry) as [[mid Run] Sound].
 split.
 - destruct(LadderEntry.checked _ _ _ _ _ _ P I C Entry (Sound _ Run)) as [t [Ladder E]].
   destruct(proj1(LadderStage.checked _ _ _ _ _ I Geo E)) as [stop Stage];exists stop,q,mid,t;auto.
 - intros stop [u [t [ladder [U [T [L Stage]]]]]];rewrite Call in U;injection U as <-.
   destruct(LadderEntry.checked _ _ _ _ _ _ P I C Entry (Sound _ T)) as [v [RunL E]].
   rewrite L in RunL;injection RunL as <-;exists t,ladder;auto.
Qed.

Lemma zip pc bias e h r child score :
 placement e -> loaded Zip215 bias (mem e) (writable e) -> ProductRun.geometry (HashLayout.chunk Zip215 e bias) -> ScoreStart.reached Zip215 bias pc e h r child score ->
 (exists stop,observed Zip215 bias score stop) /\
 (forall stop,observed Zip215 bias score stop -> exists mid ladder,LadderEntry.entry Zip215 bias e mid ladder /\ LadderStage.observed bias ladder stop).
Proof. intros P I G R;apply product_checked;try assumption;exact (CandidateEntry.zip _ _ _ _ _ _ _ P R). Qed.

Theorem checked pol bias pc e h r child score :
 placement e -> loaded pol bias (mem e) (writable e) -> ProductRun.geometry (HashLayout.chunk pol e bias) -> HashLayout.active pol e -> ScoreStart.reached pol bias pc e h r child score ->
 (exists stop,observed pol bias score stop) /\
 (forall stop,observed pol bias score stop -> LinkedRun.accounted e (writable e) stop).
Proof.
 intros P I Geo Live Ready;destruct pol.
 - destruct(zip _ _ _ _ _ _ _ P I Geo Ready) as [Exists Sound];split;[exact Exists|].
   intros stop O;destruct(Sound _ O) as [mid [ladder [E Stage]]];exact (proj1(proj2(LadderStage.checked _ _ _ _ _ I Geo E) _ Stage)).
 - destruct(StrictScreen.checked _ _ _ _ _ _ _ P I Live Ready) as [Exists Sound];split;[exact Exists|].
   intros stop O;exact (StrictScreen.writes _ _ _ (Sound _ O)).
Qed.
