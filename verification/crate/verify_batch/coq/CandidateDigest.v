From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.StoreInstructions execution.WordSemantics
 abi.SysV execution.PreservedRegister execution.WordBounds execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute
 memory.Alignment memory.FlatMemory memory.ByteMemory memory.WriteTrace.
From Machine Require abi.FramePointer.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require CandidateEntry.
Import ListNotations. Local Open Scope Z_scope.

Definition child:=Radix16.LinkedBytes.wrapper_pc.
Definition origin pol bias:=bias+ScoreStart.candidate pol.
Definition enter pol bias:=segment (origin pol bias) (ScoreStart.candidate_code pol) 8.
Definition top e:=ScoreFrame.buffer e-8.
Definition dst e:=top e-16-520.
Definition saves:list line:=[(0,1%nat,SaveG 3);(1,2%nat,SaveG 12);(3,7%nat,Sub64 4 520)].
Definition send pol:list line:=[(10,3%nat,CopyG 3 7);(13,3%nat,CopyG 12 6);(16,3%nat,CopyG 7 4);
 (19,5%nat,Load64 6 (Address 12 None 80));(24,5%nat,CallRelative(child-(ScoreStart.candidate pol+29)))].
Lemma image pol:linked (ScoreStart.candidate_code pol) saves /\ linked (ScoreStart.candidate_code pol) (send pol).
Proof. destruct pol;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Lemma in_image pol:In (child,Radix16.LinkedBytes.symbol_bytes) (children pol).
Proof. apply in_or_app;left;do 9 right;left;reflexivity. Qed.
Definition spills o t s:=[qword (word(o+0)) (t-8) (regs s 3%nat);qword (word(o+1)) (t-16) (regs s 12%nat)].
Definition call_store o d:=qword (word(o+24)) (d-8) (o+29).
Lemma save pol o s c t : regs s 4%nat=t -> 544<=t<2^64 ->
 exists u k,run 3 (ScalarBytes.fetch o (ScoreStart.candidate_code pol)) (State(Running 0) s c)=
   Some(State(Running 10) u k,spills o t s) /\ regs u 4%nat=t-16-520 /\
   (forall r,r<>4%nat -> regs u r=regs s r).
Proof.
 intros SP Fit;do 2 eexists;split.
 - apply (InstructionRoute.checked _ _ _ (proj1(image pol)));cbn [saves follow step cpu_state cf loc option_map app
   snd caller_stores caller_step apply_stack stack_step result_regs result_mem target_ip with_words push push_words regs mem put Nat.eqb].
   rewrite SP;repeat match goal with |-context[word ?x]=>rewrite (word_fits x ltac:(unfold word64 in *;lia)) end.
   replace (t-8-8) with (t-16) by ring;reflexivity.
 - cbn [regs with_zf set set_regs with_words put Nat.eqb];split;[reflexivity|].
   intros r R;destruct r as [|[|[|[|[|r]]]]];congruence || reflexivity.
Qed.

Lemma invoke pol bias s c d ptr : regs s 4%nat=d -> regs s 6%nat=ptr -> 8<=d<2^64 ->
 word64(ptr+80) -> word64(bias+child) -> let o:=origin pol bias in exists u,
 run 5 (ScalarBytes.fetch o (ScoreStart.candidate_code pol)) (State(Running 10) s c)=
 Some(State(Running(child-ScoreStart.candidate pol)) u c,[call_store o d]) /\
 regs u 4%nat=d-8 /\ regs u 7%nat=d /\ regs u 6%nat=read_word (mem s) (ptr+80) /\
 regs u 3%nat=regs s 7%nat /\ regs u 12%nat=ptr.
Proof.
 intros SP Ptr Fit A Target o;eexists;split.
 - apply (InstructionRoute.checked _ _ _ (proj2(image pol)));cbn [send follow step cpu_state cf loc option_map app effective
    push push_words set set_regs with_words regs mem put Nat.eqb].
   rewrite SP,Ptr,!Z.add_0_r,(word_fits _ A),(word_fits (d-8)) by (unfold word64;lia).
   replace (o+(24+Z.of_nat 5+(child-(ScoreStart.candidate pol+29)))) with (bias+child) by (unfold o,origin;ring).
   rewrite (word_fits _ Target);replace (bias+child-o) with (child-ScoreStart.candidate pol) by (unfold o,origin;ring);reflexivity.
 - cbn [regs with_words set set_regs put Nat.eqb];repeat split;reflexivity.
Qed.
Record entry pol bias e p q:Prop:=Entry {
 pc:ip q=bias+child; writes:accounted e (writable e) q; words:well_formed(machine q);
 stack:regs(machine q) 4%nat=dst e-8; output:regs(machine q) 7%nat=dst e; input:regs(machine q) 6%nat=Rows.frame e;
 point:regs(machine q) 3%nat=ScoreFrame.buffer e; pointers:regs(machine q) 12%nat=Rows.frame e+768;
 link:read_word (mem(machine q)) (dst e-8)=origin pol bias+29;
 parent:preserved (CandidateEntry.retained e) (mem(machine p)) (mem(machine q));
 saved:forall g,In g sysv_saved -> g<>3%nat -> g<>12%nat -> regs(machine q) g=regs(machine p) g;
 memory:mem(machine q)=replay (mem(machine p)) (spills (origin pol bias) (top e) (machine p)++[call_store (origin pol bias) (dst e)]);
 store_log:log q=log p++(spills (origin pol bias) (top e) (machine p)++[call_store (origin pol bias) (dst e)])
}.

Theorem checked pol bias e p : placement e -> loaded pol bias (mem e) (writable e) -> CandidateEntry.entry pol bias e p ->
 exists q,enter pol bias p=Some q /\ entry pol bias e p q.
Proof.
 intros P I E;set (o:=origin pol bias);set (t:=top e);set (d:=dst e);set (ptr:=Rows.frame e+768).
 destruct(stack_ok _ P) as [[Low High] _];pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)) as Gap.
 assert (Fit:544<=t<2^64 /\ 8<=d<2^64 /\ word64(ptr+80)) by
   (unfold d,dst,t,top,ptr,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp,word64 in *;lia).
 destruct(save pol o (machine p) (carry p) t (CandidateEntry.stack _ _ _ _ E) (proj1 Fit)) as [u [c [A [SP G]]]].
 destruct(invoke pol bias u c d ptr SP ltac:(rewrite G by discriminate;exact (CandidateEntry.inputs _ _ _ _ E))
   (proj1(proj2 Fit)) (proj2(proj2 Fit)) (mapped_word _ _ _ I _ _ (in_image pol) ltac:(vm_compute;reflexivity)))
   as [v [B [VS [DI [SI [BX R12]]]]]];fold o in B.
 pose proof(run_append _ _ _ _ _ A _ _ _ B) as Run.
 pose proof(CandidateEntry.writes _ _ _ _ E) as Acc;destruct(mapped_now _ _ _ I _ _ _ Acc (ScoreStart.candidate_image pol)) as [Map Sep].
 set (ws:=spills o t (machine p)++[call_store o d]) in *.
 assert (Private:confined (fun x=>sp e-16384<=x<Rows.frame e) ws).
 { apply Forall_forall;intros w [<-|[<-|[<-|[]]]] x X;unfold touches in X;cbn [qword address size call_store] in X;
   change (Z.of_nat 8) with 8 in X;unfold d,dst,t,top,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia. }
 assert (Safe:confined (writable e) ws).
 { eapply Forall_impl;[|exact Private];intros w H x X;left;specialize(H x X);unfold span,Rows.frame,sp in *;lia. }
 destruct(at_segment _ _ p o _ 8 0 _ _ Acc ltac:(rewrite Z.add_0_r;exact (CandidateEntry.at_call _ _ _ _ E)) Map Sep Run Safe) as [Next Paid].
 assert (Mem:mem v=replay (mem(machine p)) ws) by exact (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Run)).
 assert (Read:read_word (mem u) (ptr+80)=Rows.frame e).
 { replace (ptr+80) with (Rows.frame e+848) by (unfold ptr;ring);etransitivity;[|exact (CandidateEntry.digest_ptr _ _ _ _ E)].
   apply preserved_read with (outside:=CandidateEntry.retained e);[|intros k K;right;change (0<=k<8) in K;lia].
   intros x X;pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ A)) as M;cbn [cpu_state] in M;rewrite M;
   apply (WriteTrace.frame _ _ (proj1(proj1(Forall_app _ _ _) Private)));unfold CandidateEntry.retained in X;lia. }
 eexists;split;[exact Next|constructor].
 - cbn [LinkedRun.finish ip];unfold absolute;cbn [loc];unfold o,origin;ring.
 - exact Paid.
 - exact (segment_wf _ _ _ _ _ (CandidateEntry.words _ _ _ _ E) Next).
 - exact VS.
 - exact DI.
 - exact (eq_trans SI Read).
 - rewrite <- (CandidateEntry.point _ _ _ _ E);change (regs v 3%nat=regs(machine p) 7%nat);rewrite BX,G by discriminate;reflexivity.
 - exact R12.
 - cbn [LinkedRun.finish machine cpu_state];rewrite Mem;unfold ws;rewrite replay_app;cbn [replay fold_left];apply write_read_word.
   destruct(symbols _ _ _ _ I _ _ (ScoreStart.candidate_image pol)) as [[L H] _].
   assert (Len:29<Z.of_nat(length(ScoreStart.candidate_code pol))) by (destruct pol;vm_compute;reflexivity).
   unfold o,origin,word64;lia.
 - intros x X;cbn [LinkedRun.finish machine cpu_state];rewrite Mem;apply (WriteTrace.frame _ _ Private);unfold CandidateEntry.retained in X;lia.
 - intros g K A3 A12;eapply (run_keeps_at g o (ScoreStart.candidate_code pol));[destruct pol;vm_compute;reflexivity| |exact Run].
   destruct K as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];try contradiction;destruct pol;vm_compute;reflexivity.
 - exact Mem.
 - reflexivity.
Qed.
