From Coq Require Import ZArith.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require ReducedDigest.

(* The two scorers diverge after their common frame allocation. ZIP calls
   the candidate immediately. Dalek starts by screening its decoded R. *)
Definition observed pol bias score stop : Prop := match pol with
 | Zip215=>exists q,CandidateDigest.enter Zip215 bias score=Some q /\ ReducedDigest.observed bias q stop
 | Dalek=>stop=score end.

Theorem checked pol bias pc e h r child score :
 placement e -> loaded pol bias (mem e) (writable e) -> ScoreStart.reached pol bias pc e h r child score ->
 (exists stop,observed pol bias score stop) /\
 (forall stop,observed pol bias score stop -> LinkedRun.accounted e (writable e) stop).
Proof.
 intros P I Ready;destruct pol.
 - pose proof(CandidateEntry.zip _ _ _ _ _ _ _ P Ready) as AtCandidate.
   destruct(CandidateDigest.checked _ _ _ _ P I AtCandidate) as [q [Call Entry]].
   destruct(ReducedDigest.checked _ _ _ _ _ P I AtCandidate Entry) as [[stop R] Sound].
   split;[exists stop,q;auto|].
   intros t [u [U T]];rewrite Call in U;injection U as <-;exact (ReducedDigest.writes _ _ _ _ _ (Sound _ T)).
 - split;[exists score;reflexivity|intros stop ->;exact (ScoreStart.accounted _ _ _ _ _ _ _ _ Ready)].
Qed.
