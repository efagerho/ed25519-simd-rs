From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch execution.ScalarBytes execution.StoreHistory
 memory.WriteTrace memory.ByteMemory.
From Machine Require abi.FramePointer.
From Ed25519Simd.FullLadder Require Import Operands.
From Ed25519Simd.FullLadder Require StageEntry Object LoopFrame.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require LadderLayout.
Import ListNotations. Local Open Scope Z_scope.
Module F := Ed25519Simd.FullLadder.Audit.
Module Entry := Ed25519Simd.FullLadder.StageEntry.
Local Notation pc := FullLadder.LinkedBytes.entry_pc.
Local Notation text := FullLadder.LinkedBytes.symbol_bytes.
Local Notation stage := FullLadder.LinkedBytes.stage_pc.
Local Notation code := StageRound.ObjectBytes.symbol_bytes.

Definition enter bias:=segment (bias+pc) text 18.
Definition resume q c :=
 let '(back,v):=S.run (ip q) (machine q) in Cursor back v c (log q++SA.writes (ip q) (machine q)).
Definition observed bias ladder stop := exists q,enter bias ladder=Some q /\ ip q=bias+stage /\
 mapped (mem(machine q)) (ip q) code /\ stop=resume q (carry stop).

Lemma in_image pol : In (stage,code) (children pol).
Proof. apply in_or_app;left;do 12 right;left;reflexivity. Qed.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Lemma loan pol bias e p t x : LadderEntry.entry pol bias e p t ->
 regs(machine t) 4%nat-5032<=x<regs(machine t) 4%nat -> writable e x.
Proof.
 intros E;rewrite (proj1 (LadderEntry.arguments _ _ _ _ _ E)).
 unfold CandidateDigest.dst,CandidateDigest.top,ScoreFrame.buffer,FramePointer.bottom.
 pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)).
 intros X;left;unfold span,ScoreFrame.top,Rows.frame,sp in *;lia.
Qed.

Definition selected ladder stop := forall k i j,(i<SA.columns k)%nat -> (j<8)%nat ->
 read_word (mem(machine stop)) (F.base_of (machine ladder)+64*Z.of_nat(SA.first_row k+i)+8*Z.of_nat j)=
 table_row (machine ladder) j (affine k) (weight (machine ladder) j 31 k) i.

Definition private_stack ladder x:=regs(machine ladder) 4%nat-5032<=x<regs(machine ladder) 4%nat.
Definition ready bias ladder stop:=well_formed(machine stop) /\ regs(machine stop) 3%nat=regs(machine ladder) 7%nat /\
 regs(machine stop) 4%nat=F.base_of(machine ladder) /\ FullLadder.LoopFrame.intact bias (machine ladder) (machine stop) /\
 StoreHistory.extends (private_stack ladder) ladder stop.

Theorem with_cpu pol bias e p t : loaded pol bias (mem e) (writable e) ->
 ProductRun.geometry (HashLayout.chunk pol e bias) -> LadderEntry.entry pol bias e p t ->
 (exists stop,observed bias t stop) /\ (forall stop,observed bias t stop ->
 accounted e (writable e) stop /\ ip stop=bias+pc+54 /\ selected t stop /\ ready bias t stop).
Proof.
 intros I Geo L;pose proof(LadderEntry.writes _ _ _ _ _ L) as Prev.
 destruct(LadderLayout.checked _ _ _ _ _ Geo L) as [Place Valid].
 destruct(mapped_now _ _ _ I _ _ _ Prev (LadderEntry.child_image pol)) as [Map _].
 destruct(F.first_stage_call FullLadder.Object.assembled_full_ladder_correct bias (machine t) (carry t)
   Place (proj1 Valid) Map) as [u [k [Run E]]].
 set (q:=Cursor (bias+stage) u k (log t++Entry.stores (bias+pc) (regs(machine t) 4%nat) (machine t))).
 assert (Call:enter bias t=Some q).
 { unfold enter,segment;rewrite (LadderEntry.at_ladder _ _ _ _ _ L),Z.sub_diag,Run.
   unfold q;cbn [option_map LinkedRun.finish absolute loc cf cpu_state];replace (bias+pc+(stage-pc)) with (bias+stage) by ring;reflexivity. }
 assert (Safe:forall ws,confined (fun x=>regs(machine t) 4%nat-5032<=x<regs(machine t) 4%nat) ws ->
   confined (writable e) ws).
 { intros ws H;eapply Forall_impl;[|exact H];intros w W x X;apply (loan _ _ _ _ _ _ L),(W x X). }
 assert (At:accounted e (writable e) q).
 { apply append_accounted;[exact Prev|apply Safe,(Entry.stage_stack_stores _ _ _ E)|].
   intro x;now rewrite (Entry.stage_memory _ _ _ E). }
 destruct(mapped_now _ _ _ I _ _ _ At (in_image pol)) as [Code _].
 pose proof(F.first_stage_return FullLadder.Object.assembled_full_ladder_correct _ _ _ Place Valid E) as Done.
 pose proof(FullLadder.LoopFrame.first _ _ _ Place Valid E) as Frame.
 destruct(S.run (bias+stage) u) as [back v] eqn:Ret in Done,Frame.
 assert (Return:forall c,resume q c=Cursor back v c (log q++SA.writes (bias+stage) u)).
 { intro c;unfold resume;change (ip q) with (bias+stage);change (machine q) with u;now rewrite Ret. }
 split.
 - exists (resume q None),q;split;[exact Call|split;[reflexivity|split;[exact Code|]]];repeat rewrite Return;reflexivity.
 - intros stop [a [A [_ [_ End]]]];rewrite Call in A;injection A as <-.
   rewrite Return in End;rewrite End;split.
   + unfold q;cbn [log];rewrite <-app_assoc;apply append_accounted;[exact Prev| |].
     * apply Safe,(F.writes _ _ _ _ _ Done).
     * exact (F.account _ _ _ _ _ Done).
   + split;[exact (F.at_continuation _ _ _ _ _ Done)|split;[exact (F.rows _ _ _ _ _ Done)|]].
     split;[exact (F.returned_words _ _ _ _ _ Done)|split;[exact (F.point_pointer _ _ _ _ _ Done)|]].
     split;[exact (F.restored_rsp _ _ _ _ _ Done)|split;[exact Frame|]].
     exists (F.stage_stores bias (machine t) u);split.
     * unfold F.stage_stores,q;cbn [log];symmetry;apply app_assoc.
     * split;[exact (F.writes _ _ _ _ _ Done)|exact (F.account _ _ _ _ _ Done)].
Qed.

Theorem checked pol bias e p t : loaded pol bias (mem e) (writable e) ->
 ProductRun.geometry (HashLayout.chunk pol e bias) -> LadderEntry.entry pol bias e p t ->
 (exists stop,observed bias t stop) /\ (forall stop,observed bias t stop ->
 accounted e (writable e) stop /\ ip stop=bias+pc+54 /\ selected t stop).
Proof.
 intros I G L;destruct(with_cpu _ _ _ _ _ I G L) as [Ex Sound];split;[exact Ex|].
 intros stop O;destruct(Sound _ O) as [A [At [Rows _]]];auto.
Qed.
End Iteration.
