From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds execution.MaskTransfer memory.ByteMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require StrictMatchBits StrictMatchBranch ScoredChunk.
Local Open Scope Z_scope.
Local Notation pc:=(ScoreSetup.callee Dalek).
Definition publish zero bias p:=bind (StrictMatchBranch.args bias zero p) (ScoreTail.execute Dalek bias).
Definition remainder bias p k:=if regs(machine p) 12%nat=?0 then publish true bias p else
 bind (StrictCoordinate.execute false bias p k) (fun '(x,_)=>publish false bias x).
Definition execute bias p bank:=bind (StrictMatchState.execute bias p) (fun ctx=>
 bind (StrictCoordinate.execute true bias ctx bank) (fun '(y,k)=>
 bind (StrictMatchBranch.test_y bias y) (fun q=>remainder bias q k))).
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition result bias parent e q:=exists t m,ScoreTail.entry bias parent e t q m /\ ScoredChunk.verdict Dalek e q m.

Lemma published (zero:bool) bias parent e caller p : placement e -> loaded Dalek bias (mem e) (writable e) ->
 ip p=bias+pc+(if zero then 554 else 549) -> accounted e (writable e) p -> well_formed(machine p) ->
 StrictMatchState.context bias parent e caller (machine p) -> 0<=regs(machine p) 0%nat<256 ->
 StrictMatchBits.verdict e (StrictMatchBranch.mask zero (machine p)) ->
 exists q,publish zero bias p=Some q /\ result bias parent e q.
Proof.
 intros P I PC Acc W C Byte Bits;set(m:=StrictMatchBranch.mask zero (machine p)) in *.
 destruct(StrictMatchBranch.arguments _ _ _ _ _ _ I PC Acc W C Byte) as [t [SetupArgs [At [Paid [Wt [Frame [Flags Args]]]]]]].
 destruct(ScoreTail.checked Dalek bias parent e caller t m P I At Paid Wt Frame Args) as [q [Tail End]].
 exists q;split;[unfold publish;now rewrite SetupArgs|exists t,m;split;[exact End|constructor]].
 - unfold m,StrictMatchBranch.mask;destruct zero;[lia|apply EligibleLanes.masked_byte,Byte].
 - intros j J;unfold ScoredChunk.flags;rewrite (ScoreTail.memory _ _ _ _ _ _ End);exact(proj1(Flags j J)).
 - intros j J;unfold ScoredChunk.flags;rewrite (ScoreTail.memory _ _ _ _ _ _ End),(proj2(Flags j J)),(Bits j J);
   split;[tauto|intro A;exact(conj (Optimized.accepted_eligible _ _ A) A)].
Qed.

Theorem checked bias parent e caller p bank:placement e -> loaded Dalek bias (mem e) (writable e) ->
 StrictResume.result bias parent e caller p ->
 exists q,execute bias p bank=Some q /\ result bias parent e q.
Proof.
 intros P I Ret;destruct(StrictMatchState.checked _ _ _ _ _ I Ret) as [ctx [Setup [Start [Paid [W [Frame Live]]]]]].
 destruct(StrictCoordinate.checked true bias parent e caller ctx bank P I Start Paid W Frame) as [y [k [First Y]]].
 destruct(StrictMatchBranch.tested _ _ _ _ _ P I (StrictCoordinate.address _ _ _ _ _ _ _ Y)
  (StrictCoordinate.writes _ _ _ _ _ _ _ Y) (StrictCoordinate.words _ _ _ _ _ _ _ Y) (StrictCoordinate.context _ _ _ _ _ _ _ Y)
  (StrictCoordinate.mask_byte _ _ _ _ _ _ _ Y)) as [v [Gate [At [A [Wv [C [M AX]]]]]]].
 assert (Ymask:StrictMatchBits.y_mask e (regs(machine v) 12%nat)).
 { rewrite M;apply StrictMatchBits.vertical;[rewrite (StrictCoordinate.active _ _ _ _ _ _ _ Y),Live;exact(StrictResume.live _ _ _ _ _ Ret)|
   exact(StrictCoordinate.coordinates _ _ _ _ _ _ _ Y)]. }
 unfold execute;rewrite Setup;cbn [bind];rewrite First;cbn [bind];rewrite Gate;cbn [bind];unfold remainder.
 unfold StrictMatchBranch.next in At;destruct(regs(machine v) 12%nat=?0) eqn:Empty.
 - apply Z.eqb_eq in Empty;rewrite Empty in Ymask;apply(published true bias parent e caller v P I At A Wv C);
     [rewrite AX;exact(StrictCoordinate.mask_byte _ _ _ _ _ _ _ Y)|exact(StrictMatchBits.zero _ Ymask)].
 - destruct(StrictCoordinate.checked false bias parent e caller v k P I At A Wv C) as [x [k' [Second X]]].
   rewrite Second;cbn [bind];apply (published false bias parent e caller x P I (StrictCoordinate.address _ _ _ _ _ _ _ X)
    (StrictCoordinate.writes _ _ _ _ _ _ _ X) (StrictCoordinate.words _ _ _ _ _ _ _ X) (StrictCoordinate.context _ _ _ _ _ _ _ X)
    (StrictCoordinate.mask_byte _ _ _ _ _ _ _ X)).
   apply StrictMatchBits.horizontal;[rewrite (StrictCoordinate.active _ _ _ _ _ _ _ X);exact Ymask|exact(StrictCoordinate.coordinates _ _ _ _ _ _ _ X)].
Qed.
End Iteration.
