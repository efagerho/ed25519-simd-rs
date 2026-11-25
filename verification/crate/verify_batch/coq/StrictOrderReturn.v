From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds execution.WordSemantics
 execution.MappedFetch memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Machine Require execution.MaskReturn abi.FramePointer.
From Curve25519.group Require Import Affine Representation.
From Ed25519Simd.SmallOrder Require Object.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require StrictRCall.
Import ListNotations. Local Open Scope Z_scope.
Module S:=SmallOrder.Audit.
Local Notation pc:=SmallOrder.EntryBytes.address.
Local Notation text:=SmallOrder.EntryBytes.symbol_bytes.
Local Notation helper:=SmallOrder.HelperBytes.address.
Local Notation literals:=SmallOrder.HelperBytes.symbol_bytes.
Definition execute bias:=S.execute bias pc helper 3.
Lemma helper_image:In (helper,literals) (children Dalek).
Proof. apply in_or_app;right;do 5 right;left;reflexivity. Qed.
Definition region e x:=ScoreFrame.buffer e-32<=x<ScoreFrame.buffer e-8.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Lemma layout bias e prev p : placement e -> loaded Dalek bias (mem e) (writable e) ->
 accounted e (writable e) p -> StrictRCall.called e bias prev p ->
 S.placement bias pc text helper literals 3 p /\
 forall x,region e x -> writable e x.
Proof.
 intros P I Acc [At [SP [Ptr _]]];destruct(stack_ok _ P) as [[L H] _];destruct(scratch_ok _ P) as [[D End] Al].
 pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)) as Gap.
 assert (Safe:forall x,region e x -> writable e x) by (intros x X;left;unfold region,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,span,sp in *;lia).
 destruct(mapped_now _ _ _ I _ _ _ Acc StrictRCall.child_image) as [Map Sep].
 destruct(mapped_now _ _ _ I _ _ _ Acc helper_image) as [M' Sep'].
 split;[constructor|exact Safe].
 - exact At.
 - rewrite SP;unfold ScoreFrame.buffer,FramePointer.bottom;set (a:=ScoreFrame.top e-48).
   replace (a-a mod 64-1280-8) with (56+(a/64-21)*64) by (pose proof(Z.div_mod a 64 ltac:(lia));lia).
   rewrite Z.mod_add by lia;reflexivity.
 - rewrite SP;unfold fits64,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia.
 - rewrite Ptr;unfold fits64,BatchDecode.point,BatchDecode.point_offset;lia.
 - exact (conj Map M').
 - intros x [Code|[Other|Point]];rewrite SP.
   + intro X;apply (Sep x Code),Safe;unfold region;lia.
   + intro X;apply (Sep' x Other),Safe;unfold region;lia.
   + rewrite Ptr in Point;destruct(scratch_stack _ P);unfold S.extent,BatchDecode.point,BatchDecode.point_offset,FlatMemory.disjoint,
       ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia.
Qed.
Record result bias e p q:Prop:=Result {
 address:ip q=bias+ScoreSetup.callee Dalek+170;
 writes:accounted e (writable e) q; words:well_formed(machine q);
 rsp:regs(machine q) 4%nat=ScoreFrame.buffer e;
 gprs:forall g,g<>0%nat -> g<>4%nat -> regs(machine q) g=regs(machine p) g;
 frame:preserved (fun x=>~region e x) (mem(machine p)) (mem(machine q));
 byte:0<=regs(machine q) 0%nat<256;
 weak:forall j R,(j<8)%nat -> Policy.decodes (BatchDecode.original_encoding true e j) R ->
    (Z.testbit (regs(machine q) 0%nat) (Z.of_nat j)=true <-> multiple 8 R=identity)
}.
Theorem checked bias e prev p ks : placement e -> loaded Dalek bias (mem e) (writable e) ->
 accounted e (writable e) p -> well_formed(machine p) -> StrictRCall.called e bias prev p ->
 exists q bank,execute bias p ks=Some(q,bank) /\ result bias e p q.
Proof.
 intros P I Acc W Call;destruct(layout _ _ _ _ P I Acc Call) as [Place Loan].
 destruct Call as [_ [SP [Ptr [Link [_ [_ Geo]]]]]].
 assert (Point:S.point_at p=DecodedRows.buffer true e (machine p)) by (unfold S.point_at,DecodedRows.buffer;now rewrite Ptr).
 assert (B:S.bounded(S.point_at p)).
 { rewrite Point;intros i j K J;apply (proj1 Geo);lia. }
 destruct(S.machine_return bias pc text helper literals 3 p ks SmallOrder.Object.assembled_small_order_correct ltac:(lia) Place W B)
   as [q [bank [m [Run [Ret [_ [Byte [AX Bits]]]]]]]].
 pose proof(MaskReturn.stores _ _ _ _ _ _ _ _ Ret) as Safe;rewrite SP in Safe.
 assert (Slot:confined (region e) (MaskReturn.saved_log bias 3 (S.raw pc helper 3) (S.inputs(S.point_at p)) p)).
 { eapply Forall_impl;[|exact Safe];intros z H x X;specialize(H x X);change (ScoreFrame.buffer e-8-24<=x<ScoreFrame.buffer e-8) in H;change (ScoreFrame.buffer e-32<=x<ScoreFrame.buffer e-8);lia. }
 assert (Paid:accounted e (writable e) q).
 { destruct Acc as [Prior Mem];split.
   - rewrite (MaskReturn.history _ _ _ _ _ _ _ _ Ret);apply Forall_app;split;[exact Prior|].
     eapply Forall_impl;[|exact Slot];intros z H x X;apply Loan,(H x X).
   - intros x;rewrite (MaskReturn.history _ _ _ _ _ _ _ _ Ret),replay_app,(MaskReturn.memory _ _ _ _ _ _ _ _ Ret);apply replay_equal,Mem. }
 destruct(proj1(symbols _ _ _ _ I _ _ (ScoreSetup.image Dalek))) as [L H];change (bias+ScoreSetup.callee Dalek+584<=2^64) in H.
 destruct(stack_ok _ P) as [[Bottom Top] _];pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)).
 exists q,bank;split;[exact Run|constructor].
 - rewrite (MaskReturn.back _ _ _ _ _ _ _ _ Ret),SP,Link;apply word_fits;unfold word64;lia.
 - exact Paid.
 - exact (MaskReturn.words _ _ _ _ _ _ _ _ Ret).
 - rewrite (MaskReturn.stack _ _ _ _ _ _ _ _ Ret),SP;replace (ScoreFrame.buffer e-8+8) with (ScoreFrame.buffer e) by ring.
   apply word_fits;unfold word64,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia.
 - exact (MaskReturn.other _ _ _ _ _ _ _ _ Ret).
 - intros x X;rewrite (MaskReturn.memory _ _ _ _ _ _ _ _ Ret);apply (WriteTrace.frame _ _ Slot),X.
 - now rewrite AX.
 - intros j R J Original;rewrite AX;apply (proj2(Bits j J) R);rewrite Point.
   exact (proj1(proj1(proj2(proj2 Geo) j R J Original))).
Qed.
End Iteration.
