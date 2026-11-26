From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch execution.WordBounds execution.WordSemantics
 execution.StoreHistory abi.SysV memory.FlatMemory memory.ByteMemory memory.WriteTrace memory.MemoryGeometry.
From Machine Require execution.MaskReturn abi.FramePointer.
From Curve25519.group Require Import Affine Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Torsion Require Object Native.
From Ed25519Simd.Zip215 Require Object.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require ZipTorsionCall.
Local Open Scope Z_scope.
Module N:=Torsion.Native.
Local Notation target:=Decode.HelperBytes.address.
Local Notation image:=Decode.HelperBytes.symbol_bytes.
Local Notation pc:=(ScoreSetup.callee Zip215).
Definition execute bias:=N.execute (bias+target) 3.
Definition area e x:=ScoreFrame.buffer e-1040<=x<ScoreFrame.buffer e-8.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Lemma layout bias parent e caller p:placement e -> loaded Zip215 bias (mem e) (writable e) ->
 ZipTorsionCall.called bias parent e caller p ->
 N.placement (bias+target) image 3 p /\ forall x,area e x -> writable e x.
Proof.
 intros P I Call;destruct(stack_ok _ P) as [[L H] _];destruct(scratch_ok _ P) as [[D DH] _].
 pose proof(ZipTorsionCall.stack _ _ _ _ _ Call) as SP;pose proof(ZipTorsionCall.point _ _ _ _ _ Call) as DI.
 pose proof(ZipTorsionCall.decoded _ _ _ _ _ Call) as SI;pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)) as Pad.
 assert (Safe:forall x,area e x -> writable e x) by (intros x X;left;unfold area,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp,span in *;lia).
 destruct(mapped_now _ _ _ I _ _ _ (ZipTorsionCall.writes _ _ _ _ _ Call) ZipTorsionCall.child_image) as [Code Sep].
 split;[constructor|exact Safe].
 - exact (ZipTorsionCall.address _ _ _ _ _ Call).
 - rewrite SP;unfold ScoreFrame.buffer,FramePointer.bottom;set(a:=ScoreFrame.top e-48).
   replace (a-a mod 64-1280-8) with (56+(a/64-21)*64) by (pose proof(Z.div_mod a 64 ltac:(lia));lia).
   rewrite Z.mod_add by lia;reflexivity.
 - rewrite SP;unfold fits64,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia.
 - intros b [->| ->];[rewrite DI|rewrite SI];unfold fits64,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp,BatchDecode.point,BatchDecode.point_offset in *;lia.
 - exact Code.
 - intros x [Text|[b [[->| ->] X]]];unfold N.stack;rewrite SP.
   + intros Bad;apply (Sep x Text),Safe;unfold area;lia.
   + unfold N.operand in X;rewrite DI in X;lia.
   + unfold N.operand in X;rewrite SI in X;destruct(scratch_stack _ P);unfold disjoint,BatchDecode.point,BatchDecode.point_offset,
       ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia.
Qed.

(* The scatter instruction intersects eligibility with the mask. Before that
   intersection the arithmetic result is specified for each eligible lane. *)
Definition bit q j:=Z.testbit (regs(machine q) 0%nat) (Z.of_nat j)=true.
Record result bias parent e caller q:Prop:=Result {
 back:ip q=bias+pc+62; writes:accounted e (writable e) q; words:well_formed(machine q);
 frame:ScoreSaved.frame bias parent e caller (machine q); outputs:StrictScoreFrame.outputs e (machine q);
 valid:ZipResume.live e (machine q); flags:ZipResume.flags e (machine q);
 byte:0<=regs(machine q) 0%nat<256;
 accepts:forall j,(j<8)%nat -> HashLayout.eligible Zip215 e j ->
   (bit q j <-> signature_accepts Zip215 (HashLayout.row e j))
}.

Theorem checked bias parent e caller p bank:placement e -> loaded Zip215 bias (mem e) (writable e) ->
 ZipTorsionCall.called bias parent e caller p -> exists q ks,execute bias p bank=Some(q,ks) /\
 N.prefix_inputs (bias+target) image 3 p /\ result bias parent e caller q.
Proof.
 intros P I Call;destruct(layout _ _ _ _ _ P I Call) as [Place Loan].
 assert (DI:N.point p 7%nat=ScorePoint.accumulator e (machine p)) by
  (unfold N.point,ScorePoint.accumulator;now rewrite (ZipTorsionCall.point _ _ _ _ _ Call)).
 assert (SI:N.point p 6%nat=DecodedRows.buffer true e (machine p)) by
  (unfold N.point,DecodedRows.buffer;now rewrite (ZipTorsionCall.decoded _ _ _ _ _ Call)).
 destruct(ZipTorsionCall.operands _ _ _ _ _ Call) as [Bound Group [Bounds [Ys Geo]]].
 assert (Inputs:Torsion.Audit.input_bounds (N.point p 7%nat) (N.point p 6%nat)).
 { rewrite DI,SI;intros row j R J;split;[exact (strict_split _ Bound _ _ R J)|intro;apply Bounds;assumption]. }
 pose proof(proj1(proj2 Zip215.Object.image_ok)) as Image.
 destruct(N.checked (bias+target) image 3 p bank ltac:(rewrite Image;apply Torsion.Object.assembled_torsion_correct)
   ltac:(lia) Place (ZipTorsionCall.words _ _ _ _ _ Call) Inputs) as [q [ks [m [Run [Ret [Pre [Byte [AX Bits]]]]]]]].
 pose proof(ZipTorsionCall.stack _ _ _ _ _ Call) as SP.
 pose proof(MaskReturn.stores _ _ _ _ _ _ _ _ Ret) as Stores;rewrite SP in Stores.
 assert (Hist:StoreHistory.extends (area e) p q).
 { exists (MaskReturn.saved_log (bias+target) 3 (N.raw 3) (N.rows p) p).
   split;[exact (MaskReturn.history _ _ _ _ _ _ _ _ Ret)|split].
   - eapply Forall_impl;[|exact Stores];intros w H x X;specialize(H x X);change (ScoreFrame.buffer e-8-1032<=x<ScoreFrame.buffer e-8) in H;change (ScoreFrame.buffer e-1040<=x<ScoreFrame.buffer e-8);lia.
   - intro x;now rewrite (MaskReturn.memory _ _ _ _ _ _ _ _ Ret). }
 pose proof(StoreHistory.preserves _ _ _ Hist) as Same.
 pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)) as Pad.
 pose proof(MaskReturn.other _ _ _ _ _ _ _ _ Ret) as Keep.
 exists q,ks;split;[exact Run|split;[exact Pre|constructor]].
 - rewrite (MaskReturn.back _ _ _ _ _ _ _ _ Ret),SP,(ZipTorsionCall.link _ _ _ _ _ Call);apply word_fits.
   destruct(proj1(symbols _ _ _ _ I _ _ (ScoreSetup.image Zip215))) as [L H];change (bias+pc+93<=2^64) in H;unfold word64;lia.
 - exact (StoreHistory.account _ _ _ _ (ZipTorsionCall.writes _ _ _ _ _ Call) (StoreHistory.lend _ _ _ _ Loan Hist)).
 - exact (MaskReturn.words _ _ _ _ _ _ _ _ Ret).
 - eapply ScoreSaved.keep;[exact (ZipTorsionCall.frame _ _ _ _ _ Call)|apply Keep;discriminate|].
   intros x X;apply Same;unfold ScoreSaved.area,area,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,Return.sp in *;lia.
 - eapply StrictScoreFrame.keep_outputs;[exact (ZipTorsionCall.outputs _ _ _ _ _ Call)|].
   intros g G;apply Keep;intros Eq;subst;cbv [sysv_saved In] in G;intuition discriminate.
 - intros j J;rewrite Keep by discriminate;apply (ZipTorsionCall.mask _ _ _ _ _ Call),J.
 - intros j J;cbv zeta;rewrite Same;[exact (ZipTorsionCall.eligibility _ _ _ _ _ Call j J)|].
   unfold area,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top in *;lia.
 - now rewrite AX.
 - intros j J On;unfold bit;rewrite AX.
   destruct On as [S [[R DR] [A [DA _]]]].
   assert (On:HashLayout.eligible Zip215 e j) by (split;[exact S|split;[now exists R|exists A;split;[exact DA|discriminate]]]).
   destruct(Geo j R J DR) as [Rep Z1].
   pose proof(proj2(Bits j J) (ScorePoint.product e j A) R) as Law;rewrite DI,SI in Law.
   specialize(Law (Group j A J On DA) Rep Z1).
   exact (iff_trans Law (Optimized.zip215_decoded _ _ _ S DA DR)).
Qed.
End Iteration.
