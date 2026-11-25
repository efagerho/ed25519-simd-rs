From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.InstructionRoute execution.ScalarWords execution.StoreHistory execution.MappedFetch
 memory.ByteMemory memory.FlatMemory memory.MemoryGeometry memory.WriteTrace abi.SysV.
From Machine Require abi.FramePointer.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require ZipResume.
Import ListNotations. Local Open Scope Z_scope.
Local Notation pc:=(ScoreSetup.callee Zip215).
Local Notation text:=(ScoreSetup.code Zip215).
Local Notation target:=Decode.HelperBytes.address.
Definition path:list line:=[(51,3%nat,CopyG 7 4);(54,3%nat,CopyG 6 3);(57,5%nat,CallRelative(target-(pc+62)))].
Lemma code:linked text path.
Proof. repeat constructor;vm_compute;reflexivity || discriminate. Qed.
Lemma child_image:In (target,Decode.HelperBytes.symbol_bytes) (children Zip215).
Proof. apply in_or_app;left;do 7 right;left;reflexivity. Qed.
Definition execute bias:=segment (bias+pc) text 3.
Definition slot e x:=ScoreFrame.buffer e-8<=x<ScoreFrame.buffer e.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record called bias parent e caller q:Prop:=Called {
 address:ip q=bias+target; words:well_formed(machine q); writes:accounted e (writable e) q;
 stack:regs(machine q) 4%nat=ScoreFrame.buffer e-8; point:regs(machine q) 7%nat=ScoreFrame.buffer e;
 decoded:regs(machine q) 6%nat=BatchDecode.point e true;
 link:read_word (mem(machine q)) (ScoreFrame.buffer e-8)=bias+pc+62;
 frame:ScoreSaved.frame bias parent e caller (machine q); outputs:StrictScoreFrame.outputs e (machine q);
 mask:ZipResume.live e (machine q); eligibility:ZipResume.flags e (machine q); operands:ScorePoint.points Zip215 e (machine q)
}.

Theorem checked bias parent e caller p : placement e -> loaded Zip215 bias (mem e) (writable e) ->
 ZipResume.ready bias parent e caller p -> exists q,execute bias p=Some q /\ called bias parent e caller q.
Proof.
 intros P I Before;set (s:=machine p);set (base:=ScoreFrame.buffer e);set (o:=bias+pc).
 pose proof(ZipResume.stack _ _ _ _ _ Before) as SP;fold s base in SP.
 pose proof(ZipResume.decoded _ _ _ _ _ Before) as BX;fold s in BX.
 set (u:=push (set (set s 7 base) 6 (regs s 3%nat)) (o+62)).
 set (w:=qword (word(o+57)) (base-8) (o+62)).
 pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)) as Gap.
 destruct(stack_ok _ P) as [[Low High] _].
 assert (Fit:word64(base-8)) by (unfold base,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp,word64 in *;lia).
 pose proof(mapped_word _ _ _ I _ _ child_image ltac:(vm_compute;reflexivity)) as Dest.
 assert (Run:run 3 (ScalarBytes.fetch o text) (State(Running 51) s (carry p))=Some(State(Running(target-pc)) u (carry p),[w])).
 { apply (InstructionRoute.checked _ _ _ code);cbn [path follow step loc cf cpu_state option_map app];unfold u,w.
   cbn [push push_words set set_regs with_words regs mem put Nat.eqb];rewrite SP,(word_fits _ Fit).
   replace (o+(57+Z.of_nat 5+(target-(pc+62)))) with (bias+target) by (unfold o;ring);rewrite (word_fits _ Dest).
   replace (bias+target-o) with (target-pc) by (unfold o;ring);reflexivity. }
 pose proof(ZipResume.writes _ _ _ _ _ Before) as Paid;destruct(mapped_now _ _ _ I _ _ _ Paid (ScoreSetup.image Zip215)) as [Map Sep].
 assert (Loan:forall x,slot e x -> writable e x) by (intros x X;left;unfold slot,span,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia).
 assert (Safe:confined (slot e) [w]) by (constructor;[intros x X;change (base-8<=x<base-8+8) in X;unfold slot;fold base;lia|constructor]).
 destruct(StoreHistory.segment_checked _ o text 3 p 51 _ _ (ZipResume.at_return _ _ _ _ _ Before)
   Map ltac:(intros x X Y;exact (Sep x X (Loan x Y))) Run Safe) as [Next Hist].
 pose proof(StoreHistory.preserves _ _ _ Hist) as Preserve.
 assert (Mem:mem u=commit (mem s) w) by exact (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Run)).
 assert (Kept:forall g,In g sysv_saved -> regs u g=regs s g) by (intros g [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];reflexivity).
 eexists;split;[exact Next|constructor].
 - cbn [LinkedRun.finish ip absolute loc];unfold o;ring.
 - exact (segment_wf _ _ _ _ _ (ZipResume.words _ _ _ _ _ Before) Next).
 - exact (StoreHistory.account _ _ _ _ Paid (StoreHistory.lend _ _ _ _ Loan Hist)).
 - change (word(regs s 4%nat-8)=base-8);now rewrite SP,(word_fits _ Fit).
 - reflexivity.
 - exact BX.
 - change (read_word (mem u) (base-8)=bias+pc+62);rewrite Mem;apply write_read_word.
   destruct(proj1(symbols _ _ _ _ I _ _ (ScoreSetup.image Zip215))) as [L H];change (bias+pc+93<=2^64) in H;unfold word64,o;lia.
 - eapply ScoreSaved.keep;[exact (ZipResume.frame _ _ _ _ _ Before)|reflexivity|intros x X;apply Preserve;unfold slot,ScoreSaved.area,ScoreFrame.buffer,FramePointer.bottom in *;lia].
 - apply (StrictScoreFrame.keep_outputs _ s u (ZipResume.outputs _ _ _ _ _ Before) Kept).
 - exact (ZipResume.mask _ _ _ _ _ Before).
 - intros j J;cbv zeta;rewrite Preserve;[exact (ZipResume.eligibility _ _ _ _ _ Before j J)|].
   unfold slot,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top in *;lia.
 - eapply ScorePoint.keep_points;[|exact (ZipResume.operands _ _ _ _ _ Before)].
   intros x X;apply Preserve;destruct(scratch_stack _ P);unfold FlatMemory.disjoint,slot,span,
     BatchDecode.point,BatchDecode.point_offset,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia.
Qed.
End Iteration.
