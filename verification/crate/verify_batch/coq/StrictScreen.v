From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require StrictScoreFrame.
Local Open Scope Z_scope.

(* Retain the predicate bank produced by the Y comparison until the callee's
   own instructions replace it. Its CPU return supplies EAX to NOT/AND/JE. *)
Definition execute bias t k:=bind (StrictRCall.execute bias t) (fun child=>
 if regs(machine t) 12%nat=?0 then Some child else
 bind (StrictOrderReturn.execute bias child k) (fun '(r,_)=>StrictRClear.execute bias r)).
Definition observed bias score stop:=exists ks k y t bank,
 StrictRStart.execute bias score ks=Some(y,k) /\ StrictRCanonical.execute bias y k=Some(t,bank) /\
 execute bias t bank=Some stop.
Record decision bias e stop:Prop:=Decision {
 writes:accounted e (writable e) stop; words:well_formed(machine stop);
 mask_byte:0<=regs(machine stop) 12%nat<256;
 lane:forall j,(j<8)%nat -> (Z.testbit (regs(machine stop) 12%nat) (Z.of_nat j)=true <-> StrictOrderClear.eligible e j);
 address:if regs(machine stop) 12%nat=?0 then
    ip stop=bias+ScoreSetup.callee Dalek+565 \/ ip stop=bias+ScoreSetup.callee Dalek+554
    else ip stop=bias+ScoreSetup.callee Dalek+181
}.
Lemma from_canonical bias parent e h r child score y t bank :
 placement e -> loaded Dalek bias (mem e) (writable e) ->
 ScoreStart.reached Dalek bias parent e h r child score -> StrictRStart.reached bias e score y ->
 StrictRCanonical.result bias e y t ->
 (exists q,execute bias t bank=Some q) /\ (forall q,execute bias t bank=Some q -> decision bias e q /\ StrictScoreFrame.context bias parent e child q).
Proof.
 intros P I Start Y C;destruct(StrictRCall.checked _ _ _ _ _ _ P I (StrictRFrame.checked _ _ _ _ _ _ _ _ _ P Start Y C) C)
    as [call [Step R]].
 destruct(StrictScoreFrame.at_call _ _ _ _ _ _ _ _ _ _ P Start Y C R) as [Saved Outputs].
 pose proof(StrictRCall.branch _ _ _ _ R) as Branch.
 unfold execute;rewrite Step;cbn [bind];destruct(Z.eqb_spec (regs(machine t) 12%nat) 0) as [NoneLeft|Live].
 - split;[eauto|];intros q E;injection E as <-;split;[constructor|exact (StrictScoreFrame.rejected _ _ _ _ _ _ Saved Outputs Branch (eq_trans (StrictRCall.mask _ _ _ _ R) NoneLeft))].
   + exact (StrictRCall.writes _ _ _ _ R).
   + exact (StrictRCall.words _ _ _ _ R).
   + rewrite (StrictRCall.mask _ _ _ _ R),NoneLeft;lia.
   + intros j J;rewrite (StrictRCall.mask _ _ _ _ R),NoneLeft,Z.bits_0;split;[discriminate|].
     intros [On _];pose proof(proj2(StrictRCanonical.lane _ _ _ _ C j J) On) as Enabled.
     now rewrite NoneLeft,Z.bits_0 in Enabled.
   + rewrite (StrictRCall.mask _ _ _ _ R),NoneLeft;left;exact (proj1 Branch).
 - destruct(StrictOrderReturn.checked _ _ _ _ bank P I (StrictRCall.writes _ _ _ _ R) (StrictRCall.words _ _ _ _ R) Branch)
       as [ret [k [Run End]]].
   destruct(StrictOrderClear.checked _ _ _ _ _ _ I C R End) as [q [Screen Post]].
   rewrite Run;cbn [bind];split;[eauto|];intros stop S;rewrite Screen in S;injection S as <-;split;[constructor|exact (StrictScoreFrame.screened _ _ _ _ _ _ _ Saved Outputs End Post
       (StrictCandidateInputs.after_screen _ _ _ _ _ _ _ _ _ _ _ _ P Start Y C Branch End Post))].
   + exact (StrictOrderClear.writes _ _ _ _ Post).
   + exact (StrictOrderClear.words _ _ _ _ Post).
   + exact (StrictOrderClear.mask_byte _ _ _ _ Post).
   + exact (StrictOrderClear.lane _ _ _ _ Post).
   + pose proof(StrictOrderClear.pc _ _ _ _ Post) as PC;destruct(regs(machine q) 12%nat=?0);auto.
Qed.

Theorem with_frame bias parent e h r child score : placement e -> loaded Dalek bias (mem e) (writable e) ->
 HashLayout.active Dalek e -> ScoreStart.reached Dalek bias parent e h r child score ->
 (exists stop,observed bias score stop) /\ (forall stop,observed bias score stop -> decision bias e stop /\ StrictScoreFrame.context bias parent e child stop).
Proof.
 intros P I Live Start;split.
 - set (ks:=fun _ _:nat=>false);destruct(StrictRStart.checked _ _ _ _ _ _ _ ks P I Live Start) as [y [k [First Y]]].
   destruct(StrictRCanonical.checked _ _ _ _ _ _ _ _ k P I Start Y) as [t [bank [Run C]]].
   destruct(proj1(from_canonical _ _ _ _ _ _ _ _ _ bank P I Start Y C)) as [q End];exists q,ks,k,y,t,bank;auto.
 - intros stop [ks [k [y [t [bank [F [C E]]]]]]].
   destruct(StrictRStart.checked _ _ _ _ _ _ _ ks P I Live Start) as [u [ko [First Y]]];rewrite F in First;injection First as <- <-.
   destruct(StrictRCanonical.checked _ _ _ _ _ _ _ _ k P I Start Y) as [u [ko [Run Post]]];rewrite C in Run;injection Run as <- <-.
   exact (proj2(from_canonical _ _ _ _ _ _ _ _ _ bank P I Start Y Post) _ E).
Qed.

Theorem checked bias parent e h r child score : placement e -> loaded Dalek bias (mem e) (writable e) ->
 HashLayout.active Dalek e -> ScoreStart.reached Dalek bias parent e h r child score ->
 (exists stop,observed bias score stop) /\ (forall stop,observed bias score stop -> decision bias e stop).
Proof.
 intros P I Live Start;destruct(with_frame _ _ _ _ _ _ _ P I Live Start) as [Ex All].
 split;[exact Ex|intros q Run;exact (proj1(All _ Run))].
Qed.
