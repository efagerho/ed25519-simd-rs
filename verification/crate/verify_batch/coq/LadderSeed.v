From Coq Require Import ZArith List Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch execution.ScalarBytes
 memory.FlatMemory memory.ByteMemory memory.WriteTrace.
From Curve25519.group Require Import Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.FullLadder Require Import Operands.
From Ed25519Simd.FullLadder Require SeedPoint.
From Machine Require abi.FramePointer execution.StoreHistory.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require LadderStage.
Local Open Scope Z_scope.
Module F:=FullLadder.Audit.
Module Seed:=FullLadder.NativeSeed.
Local Notation pc:=FullLadder.LinkedBytes.entry_pc.
Local Notation text:=FullLadder.LinkedBytes.symbol_bytes.
Definition execute bias:=segment (bias+pc) text (length FullLadder.Seed.code).
Definition seeded ladder staged stop:=forall j i,(j<8)%nat -> (i<20)%nat ->
 FullLadder.SeedProjection.cell (mem(machine stop)) (regs(machine ladder) 7%nat) i j=
 FullLadder.Seed.out (Seed.lane (machine staged) (regs(machine ladder) 7%nat) (F.base_of(machine ladder)) j) i.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition result bias e ladder staged q :=
 accounted e (writable e) q /\ ip q=bias+pc+768 /\
 seeded ladder staged q /\ well_formed(machine q) /\
 (forall g,g<>0%nat -> regs(machine q) g=regs(machine staged) g) /\
 StoreHistory.extends (FullLadder.SeedPath.region (regs(machine ladder) 7%nat)) staged q.

Theorem checked pol bias e prev ladder staged : loaded pol bias (mem e) (writable e) ->
 LadderEntry.entry pol bias e prev ladder ->
 LadderStage.result bias e ladder staged ->
 exists q,execute bias staged=Some q /\ result bias e ladder staged q.
Proof.
 intros I L [Acc At Rows [W [Pt [Stack _]]] [P _]].
 destruct(mapped_now _ _ _ I _ _ _ Acc (LadderEntry.child_image pol)) as [Code Sep].
 destruct(F.seed_execution FullLadder.Object.assembled_full_ladder_correct bias (machine ladder) (machine staged) (carry staged)
     P W Pt Stack Code) as [u [ws [Run R]]].
 set (q:=Cursor (bias+pc+768) u (carry staged) (log staged++ws)).
 assert (Loan:forall x,FullLadder.SeedPath.region (regs(machine ladder) 7%nat) x -> writable e x).
 { intros x X;rewrite (proj1(proj2(LadderEntry.arguments _ _ _ _ _ L))) in X;left.
   pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia));unfold FullLadder.SeedPath.region,span,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia. }
 exists q;split.
 - unfold execute,segment;rewrite At;replace (bias+pc+54-(bias+pc)) with 54 by ring;unfold Seed.run in Run;now rewrite Run.
 - split.
   + apply append_accounted with (p:=staged);[exact Acc| |intros x;rewrite (Seed.memory _ _ _ _ _ R);reflexivity].
     eapply Forall_impl;[|exact (Seed.stores _ _ _ _ _ R)];intros w Allow x X;apply Loan,(Allow x X).
   + split;[reflexivity|split;[exact (Seed.rows _ _ _ _ _ R)|split;[exact (Seed.words _ _ _ _ _ R)|split;[exact (Seed.kept _ _ _ _ _ R)|]]]].
     exists ws;split;[reflexivity|split;[exact (Seed.stores _ _ _ _ _ R)|intro x;exact (f_equal (fun m=>m x) (Seed.memory _ _ _ _ _ R))]].
Qed.

Definition odd_point e ladder stop:=
 let w:=buffer_words (mem(machine stop)) (regs(machine ladder) 7%nat) in
 loose_xyz w /\ (forall j,(j<8)%nat -> represents_xyz (point_values w j)
   (operand_point (machine ladder) generator (LadderTables.key e) j 31 S.Odd)) /\
 forall i j,(i<5)%nat -> (j<8)%nat -> cell w (15+i)%nat j=0.

Lemma represents bias e ladder staged stop : LadderLayout.valid bias ladder ->
 valid_tables (machine ladder) generator (LadderTables.key e) ->
 LadderStage.selected ladder staged -> seeded ladder staged stop -> odd_point e ladder stop.
Proof.
 intros [_ V] Tables Staged Seeded.
 eapply (SeedPoint.checked _ _ 31%nat _ _ (F.base_of(machine ladder)) (machine staged));
 [exact V|exact Tables|lia| |exact Seeded].
 intros i j H J;exact (Staged S.Odd i j H J).
Qed.
End Iteration.
