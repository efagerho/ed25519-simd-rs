From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds abi.SysV
 memory.FlatMemory memory.ByteMemory memory.WriteTrace.
From Machine Require abi.FramePointer.
From Curve25519.group Require Import Affine Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require ScoreProduct.
Local Open Scope Z_scope.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition product e j A:=let i:=HashLayout.row e j in
 verification_point (little_endian(s_bytes i)) (challenge i) A.
Definition accumulator e s:=buffer_words (mem s) (ScoreFrame.buffer e).
Record points pol e s:Prop:=Points {
 reduced:strict (accumulator e s);
 value:forall j A,(j<8)%nat -> HashLayout.eligible pol e j ->
   decodes (little_endian(key_bytes(HashLayout.row e j))) A ->
   represents_point (LadderEntry.full pol) (point_values (accumulator e s) j) (product e j A);
 signature:PreparedInputs.signature e s
}.
Lemma returned pol bias e candidate ladder u q:placement e -> CandidateEntry.entry pol bias e candidate ->
 LadderProduct.meaning pol bias e ladder u -> CandidateReturn.result e candidate q ->
 mem(machine q)=mem(machine u) -> points pol e (machine q).
Proof.
 intros P Entry Prod Ret Mem;pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)) as Pad.
 constructor.
   + unfold accumulator;rewrite Mem;exact (LadderProduct.bound _ _ _ _ _ Prod).
   + unfold accumulator;rewrite Mem;exact (LadderProduct.value _ _ _ _ _ Prod).
   + eapply DecodedRows.keep;[|exact (PreparedInputs.signature_point _ _
       (ScoreBuffers.operands _ _ (CandidateEntry.buffers _ _ _ _ Entry)))].
     intros x X;apply (CandidateReturn.parent _ _ _ Ret);destruct(scratch_stack _ P);
     unfold CandidateFrame.outside,CandidateDigest.dst,CandidateDigest.top,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp,
       BatchDecode.point,BatchDecode.point_offset,FlatMemory.disjoint,span in *;lia.
Qed.

Lemma keep_points pol e s t : preserved (fun x=>span (ScoreFrame.buffer e) 1280 x \/ span (BatchDecode.point e true) 1280 x)
 (mem s) (mem t) -> points pol e s -> points pol e t.
Proof.
 intros Keep [Bounds Group Sig].
 assert (E:forall k,(k<160)%nat -> accumulator e t k=accumulator e s k).
 { intros k K;apply preserved_read with (outside:=span (ScoreFrame.buffer e) 1280).
   - intros x X;apply Keep;left;exact X.
   - intros i I;change (0<=i<8) in I;unfold span;lia. }
 constructor.
 - intros c j C J i I;unfold cell;rewrite E by lia;apply Bounds;assumption.
 - intros j A J On K;rewrite (point_values_ext _ _ _ E J);apply Group;assumption.
 - eapply DecodedRows.keep;[|exact Sig];intros x X;apply Keep;right;exact X.
Qed.
End Iteration.
