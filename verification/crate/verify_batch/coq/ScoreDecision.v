From Coq Require Import ZArith.
From Machine Require execution.Composition.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require StrictVerdict.

Definition finish pol bias product := match pol with
 | Dalek => Composition.with_input (fun bank => Composition.output (StrictVerdict.execute bias product bank))
 | Zip215 => Composition.followed_by (Composition.output (ZipTorsionCall.execute bias product)) (fun child =>
     Composition.with_input (fun bank =>
       Composition.followed_by (Composition.output (ZipTorsion.execute bias child bank))
         (fun '(ret,_) => Composition.output (ZipVerdict.execute bias ret))))
 end.
Definition observed pol bias screen :=
 Composition.followed_by (ScoreProduct.observed pol bias screen) (finish pol bias).
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition selected pol bias parent e stop:=exists product,ScoreProduct.selected pol bias e product /\
 match pol with Dalek=>StrictVerdict.result bias parent e stop | Zip215=>ZipVerdict.result bias parent e stop end.

Theorem checked pol bias parent e h r caller score screen :
 placement e -> loaded pol bias (mem e) (writable e) -> ProductRun.geometry (HashLayout.chunk pol e bias) ->
 Tables.mapped e bias -> Candidate.constants e -> HashLayout.active pol e ->
 ScoreStart.reached pol bias parent e h r caller score -> ScoreProgress.observed pol bias score screen ->
 ScoreProduct.rejected pol screen=false ->
 Composition.ensures (observed pol bias screen) (fun stop => accounted e (writable e) stop /\ selected pol bias parent e stop).
Proof.
 intros P I G M T Active Start Screen On.
 unfold observed. eapply Composition.sequence.
 - exact (ScoreProduct.with_origin _ _ _ _ _ _ _ _ _ P I G M T Active Start Screen On).
 - intros p [_ [PC [cand [Origin [Entry Data]]]]].
   assert (Product : ScoreProduct.selected pol bias e p) by (split; [exact PC|now exists cand]).
   destruct pol.
   + change (cand=score) in Origin; subst cand.
     destruct (ZipTorsionCall.checked _ _ _ _ _ P I (ZipResume.checked _ _ _ _ _ _ _ _ P Start PC Entry Data))
       as [child [Call Child]].
     apply (Composition.after_some Call), (Composition.each_input (fun _ _ : nat => false)).
     intro bank. destruct (ZipTorsion.checked _ _ _ _ _ bank P I Child) as [ret [ks [Done [_ Bits]]]].
     apply (Composition.after_some Done), Composition.option_result.
     destruct (ZipVerdict.checked _ _ _ _ _ P I Bits) as [stop [Tail Result]].
     destruct (ZipVerdict.entry _ _ _ _ Result) as [u [m Exit]].
     exists stop; split; [exact Tail|split; [exact (ScoreTail.writes _ _ _ _ _ _ Exit)|]].
     exists p; exact (conj Product Result).
   + destruct (proj2 (StrictScreen.with_frame _ _ _ _ _ _ _ P I Active Start) _ Screen) as [Decision Frame].
     change ((regs(machine screen) 12%nat=?0)=false) in On; apply Z.eqb_neq in On.
     pose proof (StrictResume.checked bias parent e h r caller screen cand p P I
       (ScoreStart.caller _ _ _ _ _ _ _ _ Start) Decision Frame On Origin PC Data) as Ret.
     apply (Composition.each_input (fun _ _ : nat => false)). intro bank. apply Composition.option_result.
     destruct (StrictVerdict.checked _ _ _ _ _ bank P I Ret) as [stop [Done Result]].
     destruct Result as [tail [m [Exit Bits]]].
     exists stop; split; [exact Done|split; [exact (ScoreTail.writes _ _ _ _ _ _ Exit)|]].
     exists p; split; [exact Product|now exists tail,m].
Qed.
End Iteration.
