From Ed25519Simd.VerifyBatch Require Import Policy.
From Ed25519Simd.VerifyBatch Require ScoreDecision StrictScreen.

(* The initial mask bank is unspecified. A subsequent block consumes the
   actual state and bank produced by the preceding one. *)
Lemma strict_screen_path bias score stop :
 StrictScreen.observed bias score stop <->
 exists incoming y k t bank,
   StrictRStart.execute bias score incoming=Some(y,k) /\
   StrictRCanonical.execute bias y k=Some(t,bank) /\
   StrictScreen.execute bias t bank=Some stop.
Proof.
 split.
 - intros [incoming [[y k] [Start [[t bank] [Canonical End]]]]].
   exists incoming,y,k,t,bank; auto.
 - intros [incoming [y [k [t [bank [Start [Canonical End]]]]]]].
   exists incoming,(y,k); split; [exact Start|now exists (t,bank)].
Qed.

Lemma zip_torsion_path bias product stop :
 ScoreDecision.finish Zip215 bias product stop <->
 exists child bank ret ks, ZipTorsionCall.execute bias product=Some child /\
   ZipTorsion.execute bias child bank=Some(ret,ks) /\ ZipVerdict.execute bias ret=Some stop.
Proof.
 split.
 - intros [child [Call [bank [[ret ks] [Torsion Verdict]]]]].
   exists child,bank,ret,ks; auto.
 - intros [child [bank [ret [ks [Call [Torsion Verdict]]]]]].
   exists child; split; [exact Call|exists bank,(ret,ks);auto].
Qed.
