From Coq Require Import ZArith.
From Machine Require execution.Composition.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require LadderProduct LadderStage StrictScreen.

(* The two scorers diverge after their common frame allocation. ZIP calls
   the candidate immediately. Dalek starts by screening its decoded R. *)
Definition product pol bias candidate :=
 Composition.followed_by (Composition.output (CandidateDigest.enter pol bias candidate)) (fun digest =>
 Composition.followed_by (ReducedDigest.observed bias digest) (fun reduced =>
 Composition.followed_by (Composition.output (LadderEntry.enter pol bias reduced)) (LadderStage.observed bias))).

Definition observed pol bias score stop : Prop := match pol with
 | Zip215=>product Zip215 bias score stop | Dalek=>StrictScreen.observed bias score stop end.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition context pol bias e candidate staged:=exists digest mid ladder,
 CandidateDigest.entry pol bias e candidate digest /\ ReducedDigest.returned pol bias e digest mid /\
 LadderEntry.entry pol bias e mid ladder /\ LadderStage.result bias e ladder staged.

Theorem product_checked pol bias e candidate :
 placement e -> loaded pol bias (mem e) (writable e) -> ProductRun.geometry (HashLayout.chunk pol e bias) ->
 CandidateEntry.entry pol bias e candidate ->
 Composition.ensures (product pol bias candidate) (context pol bias e candidate).
Proof.
 intros P I Geo C.
 unfold product. destruct (CandidateDigest.checked _ _ _ _ P I C) as [q [Call Entry]].
 apply (Composition.after_some Call). eapply Composition.sequence.
 - exact (ReducedDigest.checked _ _ _ _ _ P I C Entry).
 - intros mid Reduced. destruct (LadderEntry.checked _ _ _ _ _ _ P I C Entry Reduced) as [ladder [Ladder E]].
   apply (Composition.after_some Ladder). eapply Composition.consequence.
   + exact (LadderStage.checked _ _ _ _ _ I Geo E).
   + intros stop _ Stage. exists q,mid,ladder; auto.
Qed.

Lemma zip pc bias e h r child score :
 placement e -> loaded Zip215 bias (mem e) (writable e) -> ProductRun.geometry (HashLayout.chunk Zip215 e bias) -> ScoreStart.reached Zip215 bias pc e h r child score ->
 (exists stop,observed Zip215 bias score stop) /\
 (forall stop,observed Zip215 bias score stop -> context Zip215 bias e score stop).
Proof. intros P I G R;apply product_checked;try assumption;exact (CandidateEntry.zip _ _ _ _ _ _ _ P R). Qed.

Theorem checked pol bias pc e h r child score :
 placement e -> loaded pol bias (mem e) (writable e) -> ProductRun.geometry (HashLayout.chunk pol e bias) -> HashLayout.active pol e -> ScoreStart.reached pol bias pc e h r child score ->
 (exists stop,observed pol bias score stop) /\
 (forall stop,observed pol bias score stop -> LinkedRun.accounted e (writable e) stop).
Proof.
 intros P I Geo Live Ready;destruct pol.
 - destruct(zip _ _ _ _ _ _ _ P I Geo Ready) as [Exists Sound];split;[exact Exists|].
   intros stop O;destruct(Sound _ O) as [d [mid [ladder [_ [_ [_ Stage]]]]]];exact (LadderStage.paid _ _ _ _ Stage).
 - destruct(StrictScreen.checked _ _ _ _ _ _ _ P I Live Ready) as [Exists Sound];split;[exact Exists|].
   intros stop O;exact (StrictScreen.writes _ _ _ (Sound _ O)).
Qed.
End Iteration.
