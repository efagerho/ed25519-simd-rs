From Coq Require Import ZArith.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require LadderProduct StrictRStart.

(* The two scorers diverge after their common frame allocation. ZIP calls
   the candidate immediately. Dalek starts by screening its decoded R. *)
Definition observed pol bias score stop : Prop := match pol with
 | Zip215=>exists q mid,CandidateDigest.enter Zip215 bias score=Some q /\ ReducedDigest.observed bias q mid /\
                      LadderEntry.enter Zip215 bias mid=Some stop
 | Dalek=>exists ks k,StrictRStart.execute bias score ks=Some(stop,k) end.

Lemma zip pc bias e h r child score :
 placement e -> loaded Zip215 bias (mem e) (writable e) -> ScoreStart.reached Zip215 bias pc e h r child score ->
 (exists stop,observed Zip215 bias score stop) /\
 (forall stop,observed Zip215 bias score stop -> exists mid,LadderEntry.entry Zip215 bias e mid stop).
Proof.
 intros P I Ready;pose proof(CandidateEntry.zip _ _ _ _ _ _ _ P Ready) as C.
 destruct(CandidateDigest.checked _ _ _ _ P I C) as [q [Call Entry]].
 destruct(ReducedDigest.checked _ _ _ _ _ P I C Entry) as [[mid Run] Sound].
 split.
 - destruct(LadderEntry.checked _ _ _ _ _ _ P I C Entry (Sound _ Run)) as [t [Ladder _]].
   exists t,q,mid;auto.
 - intros stop [u [t [U [T L]]]];rewrite Call in U;injection U as <-.
   destruct(LadderEntry.checked _ _ _ _ _ _ P I C Entry (Sound _ T)) as [v [RunL E]].
   rewrite L in RunL;injection RunL as <-;now exists t.
Qed.

Theorem checked pol bias pc e h r child score :
 placement e -> loaded pol bias (mem e) (writable e) -> HashLayout.active pol e -> ScoreStart.reached pol bias pc e h r child score ->
 (exists stop,observed pol bias score stop) /\
 (forall stop,observed pol bias score stop -> LinkedRun.accounted e (writable e) stop).
Proof.
 intros P I Live Ready;destruct pol.
 - destruct(zip _ _ _ _ _ _ _ P I Ready) as [Exists Sound];split;[exact Exists|].
   intros stop O;destruct(Sound _ O) as [mid E];exact (LadderEntry.writes _ _ _ _ _ E).
 - split.
   + set (ks:=fun _ _:nat=>false);destruct(StrictRStart.checked _ _ _ _ _ _ _ ks P I Live Ready) as [t [k [Run _]]].
     exists t,ks,k;exact Run.
   + intros stop [ks [k Run]];destruct(StrictRStart.checked _ _ _ _ _ _ _ ks P I Live Ready) as [t [out [Next Post]]].
     rewrite Run in Next;injection Next as <- <-;exact (StrictRStart.writes _ _ _ _ Post).
Qed.
