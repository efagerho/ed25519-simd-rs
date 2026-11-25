From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.StoreHistory memory.ByteMemory.
From Machine Require abi.FramePointer.
From Curve25519.group Require Import Affine Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.FullLadder Require LoopProduct LoopFrame LoopReady TopPair.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require LadderTop.
Local Open Scope Z_scope.

Definition execute:=LoopProduct.execute.
Record meaning pol bias e ladder stop : Prop:=Meaning {
 next:ip stop=CandidateDigest.origin pol bias+LadderEntry.next pol;
 stack:regs(machine stop) 4%nat=CandidateDigest.dst e;
 saved:forall g,List.In g SysV.sysv_saved -> regs(machine stop) g=regs(machine ladder) g;
 words:well_formed(machine stop);
 bound:strict(buffer_words (mem(machine stop)) (ScoreFrame.buffer e));
 value:forall j A,(j<8)%nat -> HashLayout.eligible pol e j ->
 Policy.decodes (little_endian(key_bytes(HashLayout.row e j))) A ->
 represents_point (LadderEntry.full pol) (point_values (buffer_words (mem(machine stop)) (ScoreFrame.buffer e)) j)
   (plus (scale (little_endian(s_bytes(HashLayout.row e j))) generator)
         (scale (-Policy.challenge(HashLayout.row e j)) A))
}.

Theorem checked pol bias e prev ladder staged seed top : loaded pol bias (mem e) (writable e) -> Tables.mapped e bias ->
 Candidate.constants e -> ProductRun.geometry (HashLayout.chunk pol e bias) -> LadderEntry.entry pol bias e prev ladder ->
 LadderStage.observed bias ladder staged -> LadderSeed.execute bias staged=Some seed -> LadderTop.execute bias seed=Some top ->
 exists q,execute bias top=Some q /\ accounted e (writable e) q /\ meaning pol bias e ladder q.
Proof.
 intros I M T G L Stage Seed Top.
 destruct(LadderTop.checked _ _ _ _ _ _ _ I M T G L Stage Seed) as [v [Run [Paid Pair]]];rewrite Top in Run;injection Run as Eq;subst v.
 destruct(LadderLayout.checked _ _ _ _ _ G L) as [P V].
 destruct(proj2(LadderStage.with_cpu _ _ _ _ _ I G L) _ Stage) as [_ [_ [_ [_ [_ [_ F]]]]]].
 destruct(LadderSeed.with_history _ _ _ _ _ _ I G L Stage) as [v [R [_ [_ [_ [_ [Regs H]]]]]]];rewrite Seed in R;injection R as Eq;subst v.
 assert (SF:LoopFrame.intact bias (machine ladder) (machine seed)).
 { apply (LoopFrame.after _ _ staged seed P F);[intros g K;apply Regs;cbv [LoopFrame.live In] in K;intuition congruence|].
   eapply StoreHistory.lend;[|exact H];intros x X;left;exact X. }
 assert (TF:LoopFrame.intact bias (machine ladder) (machine top)).
 { apply (LoopFrame.after _ _ seed top P SF);[intros r K;apply (TopPair.kept _ _ _ _ _ _ Pair);cbv [LoopFrame.live In] in K;cbv [SysV.sysv_saved In];tauto|].
   eapply StoreHistory.lend;[apply LoopFrame.top_region|exact (TopPair.history _ _ _ _ _ _ Pair)]. }
 assert (Code:LoopReady.loaded bias (mem(machine top))).
 { intros a text Member;assert (Child:In (a,text) (children pol)).
   { apply in_or_app;left;do 11 right;destruct Member as [E|[E|[E|[E|[E|[]]]]]];injection E as <- <-;
     repeat first [left;reflexivity|right]. }
   exact (proj1(mapped_now _ _ _ I _ _ _ Paid Child)). }
 destruct(LadderEntry.arguments _ _ _ _ _ L) as [SP [Pt [_ [_ [_ [_ Mode]]]]]].
 destruct(LoopProduct.checked _ _ _ _ _ _ _ P V (LadderTables.supplied _ _ _ _ _ I M T L) Mode TF Code Pair) as [q [R Done]].
 exists q;split;[exact R|split].
 - eapply StoreHistory.account;[exact Paid|eapply StoreHistory.lend;[|exact (LoopProduct.stores _ _ _ _ _ _ Done)]].
   intros x [Point|Stack];[apply (LadderTop.loan _ _ _ _ _ L);left;exact Point|].
   apply (LadderStage.loan _ _ _ _ _ _ L);unfold LoopFrame.top in *;lia.
 - constructor.
   + rewrite (LoopProduct.target _ _ _ _ _ _ Done);unfold LoopFrame.top;rewrite SP;apply (LadderEntry.return_word _ _ _ _ _ L).
   + rewrite (LoopProduct.stack _ _ _ _ _ _ Done);unfold LoopFrame.top;rewrite SP;ring.
   + exact (LoopProduct.saved _ _ _ _ _ _ Done).
   + exact (LoopProduct.wf _ _ _ _ _ _ Done).
   + rewrite <-Pt;exact (LoopProduct.reduced _ _ _ _ _ _ Done).
   + intros j A J On Key;pose proof(LoopProduct.value _ _ _ _ _ _ Done j J) as Q.
     unfold LoopReady.point in Q;rewrite Pt in Q;destruct(LadderLayout.signature_digits _ _ _ _ _ _ L J) as [_ S].
     rewrite (S (proj1 On)),(proj2(LadderEntry.challenge _ _ _ _ _ L j J) On) in Q.
     assert (K:LadderTables.key e j=A).
     { unfold LadderTables.key;destruct(LadderTables.choice (BatchDecode.original_encoding false e j)) as [D|[Bad _]].
       - exact (Lane.unique_key _ _ _ D Key).
       - exfalso;exact (Bad A Key). }
     now rewrite K in Q.
Qed.
