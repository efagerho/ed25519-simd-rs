From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.ScalarWords execution.InstructionRoute execution.MappedFetch memory.FlatMemory memory.ByteMemory memory.WriteTrace.
From Machine Require abi.FramePointer.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require StrictScreen.
Import ListNotations. Local Open Scope Z_scope.
Local Notation pc:=(ScoreSetup.callee Dalek).
Local Notation text:=(ScoreSetup.code Dalek).
Local Notation callee:=(ScoreStart.candidate Dalek).

Definition path:list line:=[(181,4%nat,Load64 6 (Address 4 None 0));(185,3%nat,CopyG 7 4);
 (188,5%nat,CallRelative(callee-(pc+193)))].
Lemma image:linked text path.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute bias:=segment (bias+pc) text 3.
Definition event bias e:=qword (word(bias+pc+188)) (ScoreFrame.buffer e-8) (bias+pc+193).

Theorem checked bias parent e h r caller stop :
 placement e -> loaded Dalek bias (mem e) (writable e) -> ScoreCall.entered Dalek bias parent e h r caller ->
 StrictScreen.decision bias e stop -> StrictScoreFrame.context bias parent e caller stop ->
 regs(machine stop) 12%nat<>0 -> exists p,execute bias stop=Some p /\ CandidateEntry.entry Dalek bias e p /\
 log p=log stop++[event bias e] /\ read_word(mem(machine p))(ScoreFrame.buffer e-8)=bias+pc+193 /\
 (forall g,In g SysV.sysv_saved -> regs(machine p) g=regs(machine stop) g) /\
 preserved (fun x=>~(ScoreFrame.buffer e-8<=x<ScoreFrame.buffer e)) (mem(machine stop)) (mem(machine p)).
Proof.
 intros P I Call D F On;pose proof(StrictScoreFrame.candidate _ _ _ _ _ F On) as A.
 set (s:=machine stop) in *;set (o:=bias+pc);set (base:=ScoreFrame.buffer e).
 pose proof(StrictCandidateInputs.stack _ _ _ A) as SP;fold s base in SP.
 destruct(stack_ok _ P) as [[L H] _];pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)) as Gap.
 assert (Fit:8<=base<2^64) by (unfold base,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia).
 pose proof(mapped_word _ _ _ I _ _ (ScoreStart.candidate_image Dalek) ltac:(vm_compute;reflexivity)) as Target.
 set (u:=push (set (set s 6 (read_word (mem s) base)) 7 base) (o+193)).
 assert (Run:run 3 (ScalarBytes.fetch o text) (State(Running 181) s (carry stop))=
   Some(State(Running(callee-pc)) u (carry stop),[event bias e])).
 { apply (InstructionRoute.checked _ _ _ image);cbn [path follow step cpu_state cf loc option_map effective app].
   cbn [set set_regs with_words regs put Nat.eqb];rewrite SP,!Z.add_0_r,(word_fits base),(word_fits (base-8)) by (unfold word64 in *;lia).
   replace (o+(188+Z.of_nat 5+(callee-(pc+193)))) with (bias+callee) by (unfold o;ring);rewrite (word_fits _ Target).
   replace (bias+callee-o) with (callee-pc) by (unfold o;ring);reflexivity. }
 assert (Safe:confined (writable e) [event bias e]).
 { constructor;[intros x X;left;change (base-8<=x<base-8+8) in X;unfold base,span,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia|constructor]. }
 pose proof(StrictScreen.writes _ _ _ D) as Acc;destruct(mapped_now _ _ _ I _ _ _ Acc (ScoreSetup.image Dalek)) as [Map Sep].
 pose proof(StrictScreen.address _ _ _ D) as At;fold s in At;rewrite (proj2(Z.eqb_neq _ _) On) in At.
 destruct(at_segment _ _ stop o _ 3 181 _ _ Acc At Map Sep Run Safe) as [Next Paid].
 assert (M:mem u=commit (mem s) (event bias e)) by exact (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Run)).
 eexists;split;[exact Next|split].
 - eapply CandidateEntry.from_caller with (caller:=caller);[exact P|exact Call| | |exact Paid|exact (segment_wf _ _ _ _ _ (StrictScreen.words _ _ _ D) Next)| | |].
   + intros x X;change (mem u x=mem(machine caller) x);rewrite M;unfold commit;rewrite write_outside.
     * apply (StrictCandidateInputs.parent _ _ _ A),X.
     * change (~(base-8<=x<base-8+8));unfold base,CandidateEntry.retained,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia.
   + cbn [LinkedRun.finish ip absolute loc];unfold o;ring.
   + change (word(regs s 4%nat-8)=base-8);rewrite SP;apply word_fits;unfold word64;lia.
   + reflexivity.
   + exact (StrictCandidateInputs.slot _ _ _ A).
 - split;[reflexivity|split].
   + change (read_word (mem u) (base-8)=bias+pc+193);rewrite M;apply write_read_word.
     destruct(proj1(symbols _ _ _ _ I _ _ (ScoreSetup.image Dalek))) as [Lo Hi];change (bias+pc+584<=2^64) in Hi;unfold word64;lia.
   + split;[intros g [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];reflexivity|].
     intros x X;change (mem u x=mem s x);rewrite M;apply write_outside;change (~(base-8<=x<base-8+8));fold base in X;lia.
Qed.
