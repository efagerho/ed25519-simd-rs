From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute abi.SysV memory.FlatMemory memory.ByteMemory memory.WriteTrace.
From Machine Require abi.FramePointer.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require StrictRFrame.
Import ListNotations. Local Open Scope Z_scope.
Local Notation pc:=(ScoreSetup.callee Dalek).
Local Notation text:=(ScoreSetup.code Dalek).
Local Notation check:=SmallOrder.EntryBytes.address.

Definition invoke:list line:=[(162,3%nat,CopyG 7 3);(165,5%nat,CallRelative(check-(pc+170)))].
Definition reject:list line:=[(554,2%nat,Zero32 0);(556,3%nat,CopyG 7 13);
 (559,3%nat,CopyG 6 14);(562,3%nat,CopyG 2 15)].
Lemma image:linked text invoke /\ linked text reject.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Lemma child_image:In (check,SmallOrder.EntryBytes.symbol_bytes) (children Dalek).
Proof. apply in_or_app;right;do 4 right;left;reflexivity. Qed.

Definition execute bias p:=segment (bias+pc) text (if regs(machine p) 12%nat=?0 then 4 else 2) p.
Definition call_store bias e:=qword (word(bias+pc+165)) (ScoreFrame.buffer e-8) (bias+pc+170).
Definition rejected e bias p q:=ip q=bias+pc+565 /\ mem(machine q)=mem(machine p) /\ log q=log p /\
 regs(machine q) 0%nat=0 /\ regs(machine q) 7%nat=Rows.frame e+856 /\
 regs(machine q) 6%nat=output e /\ regs(machine q) 2%nat=regs e 6%nat /\ regs(machine q) 5%nat=ScoreFrame.top e-8.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition called e bias p q:=ip q=bias+check /\
 regs(machine q) 4%nat=ScoreFrame.buffer e-8 /\ regs(machine q) 7%nat=BatchDecode.point e true /\
 read_word (mem(machine q)) (ScoreFrame.buffer e-8)=bias+pc+170 /\
 mem(machine q)=commit (mem(machine p)) (call_store bias e) /\ log q=log p++[call_store bias e] /\
 PreparedInputs.signature e (machine q).
Record result e bias p q:Prop:=Result {
 writes:accounted e (writable e) q; words:well_formed(machine q);
 saved:forall g,In g sysv_saved -> regs(machine q) g=regs(machine p) g;
 branch:if regs(machine p) 12%nat=?0 then rejected e bias p q else called e bias p q
}.
Lemma mask e bias p q : result e bias p q -> regs(machine q) 12%nat=regs(machine p) 12%nat.
Proof. intro R;apply (saved _ _ _ _ R);simpl;tauto. Qed.

Lemma zero_raw o s c : exists u,run 4 (ScalarBytes.fetch o text) (State(Running 554) s c)=
     Some(State(Running 565) u (Some false),[]) /\
     ((forall g,In g sysv_saved -> regs u g=regs s g) /\ regs u 0%nat=0 /\ regs u 7%nat=regs s 13%nat /\
      regs u 6%nat=regs s 14%nat /\ regs u 2%nat=regs s 15%nat /\ regs u 5%nat=regs s 5%nat /\ mem u=mem s).
Proof. eexists;split;[apply (InstructionRoute.checked _ _ _ (proj2 image));reflexivity|];
 repeat split;try reflexivity;intros g [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];reflexivity. Qed.

Theorem checked bias parent e child start p : placement e -> loaded Dalek bias (mem e) (writable e) ->
 StrictRFrame.inputs bias parent e child p -> StrictRCanonical.result bias e start p ->
 exists q,execute bias p=Some q /\ result e bias p q.
Proof.
 intros P I F R;set (s:=machine p);set (o:=bias+pc);set (base:=ScoreFrame.buffer e).
 pose proof(StrictRCanonical.writes _ _ _ _ R) as Prev.
 destruct(mapped_now _ _ _ I _ _ _ Prev (ScoreSetup.image Dalek)) as [Map Sep].
 pose proof(StrictRCanonical.address _ _ _ _ R) as At;fold o in At.
 unfold execute;destruct(regs(machine p) 12%nat=?0) eqn:Zero.
 - pose proof(zero_raw o s (carry p)) as Run.
   destruct Run as [u [Run [K [Z [DI [SI [DX [FP Mem]]]]]]]].
   destruct(at_segment _ _ p o text 4 554 _ _ Prev At Map Sep Run (Forall_nil _)) as [End Paid].
   eexists;split;[exact End|constructor];[exact Paid|exact(segment_wf _ _ _ _ _ (StrictRCanonical.words _ _ _ _ R) End)|exact K|].
   rewrite Zero;unfold rejected;cbn [LinkedRun.finish ip machine log cpu_state loc absolute];rewrite app_nil_r.
   destruct(StrictRFrame.outputs _ _ _ _ _ F) as [Flags [Out N]];fold s in Flags,Out,N.
   rewrite Mem,Z,DI,SI,DX,FP,Flags,Out,N;repeat split;apply (StrictRFrame.fp _ _ _ _ _ F).
 - destruct(stack_ok _ P) as [[Bottom Top] _]. pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)) as Gap.
   assert (Fit:word64(base-8)) by (unfold base,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp,word64 in *;lia).
   destruct(proj1(symbols _ _ _ _ I _ _ (ScoreSetup.image Dalek))) as [L H];fold o in L,H;change(o+584<=2^64) in H.
   pose proof(mapped_word _ _ _ I _ _ child_image ltac:(vm_compute;reflexivity)) as Dest.
   set (arg:=set s 7 (regs s 3%nat));set (u:=push arg (o+170)).
   assert (SP:word(regs arg 4%nat-8)=base-8) by
    (change (word(regs(machine p) 4%nat-8)=base-8);rewrite (StrictRFrame.stack _ _ _ _ _ F);apply word_fits,Fit).
   assert (Run:run 2 (ScalarBytes.fetch o text) (State(Running 162) s (carry p))=
     Some(State(Running(check-pc)) u (carry p),[call_store bias e])).
   { apply (InstructionRoute.checked _ _ _ (proj1 image));cbn [invoke follow loc step cf cpu_state option_map app].
     replace (165+Z.of_nat 5) with 170 by reflexivity.
     replace (o+(170+(check-(pc+170)))) with (bias+check) by (unfold o;ring);rewrite (word_fits _ Dest).
     replace (bias+check-o) with (check-pc) by (unfold o;ring);fold arg;rewrite SP;reflexivity. }
   assert (Safe:confined (writable e) [call_store bias e]).
   { constructor;[intros x X;left;change (base-8<=x<base-8+8) in X;unfold base,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp,span in *;lia|constructor]. }
   destruct(at_segment _ _ p o text 2 162 _ _ Prev At Map Sep Run Safe) as [End Paid].
   assert (Mem:mem u=commit (mem s) (call_store bias e)).
   { change (store_word (mem s) (word(regs arg 4%nat-8)) (o+170)=commit (mem s) (call_store bias e));now rewrite SP. }
   eexists;split;[exact End|constructor];[exact Paid|exact(segment_wf _ _ _ _ _ (StrictRCanonical.words _ _ _ _ R) End)|intros g [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];reflexivity|].
   rewrite Zero;unfold called;cbn [LinkedRun.finish absolute loc ip machine log cpu_state];split;[unfold o;ring|split;[exact SP|split]].
   + exact (StrictRFrame.point _ _ _ _ _ F).
   + split;[rewrite Mem;apply write_read_word;fold o;unfold word64;lia|split;[exact Mem|split;[reflexivity|]]].
     eapply DecodedRows.keep;[|exact (StrictRFrame.rows _ _ _ _ _ F)];intros x X;rewrite Mem;apply write_outside.
     destruct(scratch_stack _ P);unfold touches,call_store;cbn [qword address size];change (Z.of_nat 8) with 8;
       unfold BatchDecode.point,BatchDecode.point_offset,span,FlatMemory.disjoint,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia.
Qed.
End Iteration.
