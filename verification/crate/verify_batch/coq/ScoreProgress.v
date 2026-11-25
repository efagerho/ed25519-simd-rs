From Coq Require Import ZArith.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require LadderProduct LadderStage StrictRCall.

(* The two scorers diverge after their common frame allocation. ZIP calls
   the candidate immediately. Dalek starts by screening its decoded R. *)
Definition observed pol bias score stop : Prop := match pol with
 | Zip215=>exists q mid ladder,CandidateDigest.enter Zip215 bias score=Some q /\ ReducedDigest.observed bias q mid /\
                      LadderEntry.enter Zip215 bias mid=Some ladder /\ LadderStage.observed bias ladder stop
 | Dalek=>exists ks k p t after,StrictRStart.execute bias score ks=Some(p,k) /\
                        StrictRCanonical.execute bias p k=Some(t,after) /\ StrictRCall.execute bias t=Some stop end.

Lemma zip pc bias e h r child score :
 placement e -> loaded Zip215 bias (mem e) (writable e) -> ProductRun.geometry (HashLayout.chunk Zip215 e bias) -> ScoreStart.reached Zip215 bias pc e h r child score ->
 (exists stop,observed Zip215 bias score stop) /\
 (forall stop,observed Zip215 bias score stop -> exists mid ladder,LadderEntry.entry Zip215 bias e mid ladder /\ LadderStage.observed bias ladder stop).
Proof.
 intros P I Geo Ready;pose proof(CandidateEntry.zip _ _ _ _ _ _ _ P Ready) as C.
 destruct(CandidateDigest.checked _ _ _ _ P I C) as [q [Call Entry]].
 destruct(ReducedDigest.checked _ _ _ _ _ P I C Entry) as [[mid Run] Sound].
 split.
 - destruct(LadderEntry.checked _ _ _ _ _ _ P I C Entry (Sound _ Run)) as [t [Ladder E]].
   destruct(proj1(LadderStage.checked _ _ _ _ _ I Geo E)) as [stop Stage];exists stop,q,mid,t;auto.
 - intros stop [u [t [ladder [U [T [L Stage]]]]]];rewrite Call in U;injection U as <-.
   destruct(LadderEntry.checked _ _ _ _ _ _ P I C Entry (Sound _ T)) as [v [RunL E]].
   rewrite L in RunL;injection RunL as <-;exists t,ladder;auto.
Qed.

Lemma dalek bias pc e h r child score :
 placement e -> loaded Dalek bias (mem e) (writable e) -> HashLayout.active Dalek e ->
 ScoreStart.reached Dalek bias pc e h r child score ->
 (exists stop,observed Dalek bias score stop) /\
 (forall stop,observed Dalek bias score stop -> exists p t,StrictRCanonical.result bias e p t /\ StrictRCall.result e bias t stop).
Proof.
 intros P I Live Ready;split.
 - set (ks:=fun _ _:nat=>false).
   destruct(StrictRStart.checked _ _ _ _ _ _ _ ks P I Live Ready) as [p [k [Start E]]].
   destruct(StrictRCanonical.checked _ _ _ _ _ _ _ _ k P I Ready E) as [t [after [Run Post]]].
   destruct(StrictRCall.checked _ _ _ _ _ _ P I (StrictRFrame.checked _ _ _ _ _ _ _ _ _ P Ready E Post) Post) as [u [Call C]].
   exists u,ks,k,p,t,after;auto.
 - intros stop [ks [k [p [t [after [Start [Run Call]]]]]]].
   destruct(StrictRStart.checked _ _ _ _ _ _ _ ks P I Live Ready) as [v [k' [S E]]].
   rewrite Start in S;injection S as <- <-.
   destruct(StrictRCanonical.checked _ _ _ _ _ _ _ _ k P I Ready E) as [v [bank [Next Post]]].
   rewrite Run in Next;injection Next as <- <-.
   destruct(StrictRCall.checked _ _ _ _ _ _ P I (StrictRFrame.checked _ _ _ _ _ _ _ _ _ P Ready E Post) Post) as [u [Next C]].
   rewrite Call in Next;injection Next as <-;exists p,t;auto.
Qed.

Theorem checked pol bias pc e h r child score :
 placement e -> loaded pol bias (mem e) (writable e) -> ProductRun.geometry (HashLayout.chunk pol e bias) -> HashLayout.active pol e -> ScoreStart.reached pol bias pc e h r child score ->
 (exists stop,observed pol bias score stop) /\
 (forall stop,observed pol bias score stop -> LinkedRun.accounted e (writable e) stop).
Proof.
 intros P I Geo Live Ready;destruct pol.
 - destruct(zip _ _ _ _ _ _ _ P I Geo Ready) as [Exists Sound];split;[exact Exists|].
   intros stop O;destruct(Sound _ O) as [mid [ladder [E Stage]]];exact (proj1(proj2(LadderStage.checked _ _ _ _ _ I Geo E) _ Stage)).
 - destruct(dalek _ _ _ _ _ _ _ P I Live Ready) as [Exists Sound];split;[exact Exists|].
   intros stop O;destruct(Sound _ O) as [p [t [_ R]]];exact (StrictRCall.writes _ _ _ _ R).
Qed.
