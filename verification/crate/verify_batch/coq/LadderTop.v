From Coq Require Import ZArith List Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch execution.StoreHistory memory.FlatMemory.
From Machine Require abi.FramePointer.
From Ed25519Simd.FullLadder Require TopPair RoundOperands Operands.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require LadderSeed.
Import ListNotations. Local Open Scope Z_scope.

Definition execute bias q:=TopPair.execute bias (regs(machine q) 4%nat) q.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition result bias e ladder seed q:=TopPair.result bias (machine ladder) generator (LadderTables.key e) seed q.

Lemma loan pol bias e prev ladder : LadderEntry.entry pol bias e prev ladder ->
 forall x,TopPair.allowed (machine ladder) x -> writable e x.
Proof.
 intros L x [Pt|Stack].
 - destruct(LadderEntry.arguments _ _ _ _ _ L) as [_ [D _]];unfold TopPair.point in Pt;rewrite D in Pt;left.
   pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia));
   unfold ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,span,sp in *;lia.
 - apply (LadderStage.loan _ _ _ _ _ _ L);unfold FullLadder.Audit.base_of,FullLadder.Program.staging,FullLadder.Audit.pad_of in *;
   pose proof(Z.mod_pos_bound (regs(machine ladder) 4%nat) 64 ltac:(lia));lia.
Qed.
Theorem checked pol bias e prev ladder staged seed :
 loaded pol bias (mem e) (writable e) -> Operands.valid_tables (machine ladder) generator (LadderTables.key e) ->
 LadderEntry.entry pol bias e prev ladder ->
 LadderStage.result bias e ladder staged -> LadderSeed.result bias e ladder staged seed ->
 exists q,execute bias seed=Some q /\ accounted e (writable e) q /\ result bias e ladder seed q.
Proof.
 intros I Tables L [_ _ Staged [_ [Pt [SP _]]] Layout] [Paid [PC [Rows [W [Regs H]]]]].
 pose proof(LadderSeed.represents _ _ _ _ _ Layout Tables Staged Rows) as [Bound [Odd _]].
 destruct Layout as [P V].
 assert (Ready:TopPair.ready bias (machine ladder) seed).
 { constructor;[exact W|now rewrite Regs by discriminate|now rewrite Regs by discriminate| |].
   - split;[exact (proj1(mapped_now _ _ _ I _ _ _ Paid (LadderEntry.child_image pol)))|].
     intro k;assert (Child:In (FullLadder.TopCall.target k,FullLadder.TopPoint.bytes k) (children pol)).
     { apply in_or_app;left;destruct k;[do 14 right;left|do 15 right;left|do 15 right;left];reflexivity. }
     exact (proj1(mapped_now _ _ _ I _ _ _ Paid Child)).
   - apply (RoundOperands.stable _ _ _ _ _ Staged);intros x X;apply (StoreHistory.preserves _ _ _ H).
     destruct(FullLadder.Native.ladder_placement _ _ _ (FullLadder.Audit.child_layout _ _ P)) as [_ _ _ _ _ _ _ _ _ Apart _].
     unfold FullLadder.SeedPath.region,disjoint in *;lia. }
 destruct(TopPair.checked bias (machine ladder) generator (LadderTables.key e) seed P V Tables Ready PC Bound Odd) as [q [Run End]].
 exists q;split;[unfold execute;rewrite (TopPair.stack _ _ _ Ready);exact Run|split;[|exact End]].
 eapply StoreHistory.account;[exact Paid|eapply StoreHistory.lend;[apply (loan _ _ _ _ _ L)|apply (TopPair.history _ _ _ _ _ _ End)]].
Qed.
End Iteration.
