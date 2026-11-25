From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute memory.ByteMemory memory.WriteTrace.
From Machine Require abi.FramePointer.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require ScoreFrame.
Import ListNotations. Local Open Scope Z_scope.

Definition candidate pol:=match pol with Zip215=>Zip215.CandidateBytes.address | Dalek=>DalekPostHash.CandidateBytes.address end.
Definition candidate_code pol:=match pol with Zip215=>Zip215.CandidateBytes.symbol_bytes | Dalek=>DalekPostHash.CandidateBytes.symbol_bytes end.
Lemma candidate_image pol:In (candidate pol,candidate_code pol) (children pol).
Proof. apply in_or_app;right;destruct pol;[right;left|do 2 right;left];reflexivity. Qed.
Definition target pol bias:=match pol with Zip215=>bias+candidate Zip215 | Dalek=>bias+ScoreSetup.callee Dalek+44 end.
Definition path pol:list line:=match pol with
 | Zip215=>[(24,3%nat,CopyG 3 6);(27,4%nat,ExtendByte 12 2);(31,3%nat,CopyG 13 1);(34,3%nat,CopyG 14 8);
            (37,3%nat,CopyG 15 9);(40,3%nat,CopyG 6 7);(43,3%nat,CopyG 7 4);
            (46,5%nat,CallRelative(candidate Zip215-(ScoreSetup.callee Zip215+51)))]
 | Dalek=>[(24,3%nat,CopyG 3 6);(27,4%nat,Store64 7 (Address 4 None 0));(31,4%nat,ExtendByte 12 2);
           (35,3%nat,CopyG 13 1);(38,3%nat,CopyG 14 8);(41,3%nat,CopyG 15 9)] end.
Lemma image pol : linked (ScoreSetup.code pol) (path pol).
Proof. destruct pol;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition o pol bias:=bias+ScoreSetup.callee pol.
Definition event pol bias t ptr:=match pol with
 | Zip215=>qword (word(o Zip215 bias+46)) (t-8) (o Zip215 bias+51)
 | Dalek=>qword (word(o Dalek bias+27)) t ptr end.
Definition execute pol bias:=segment (o pol bias) (ScoreSetup.code pol) (length(path pol)).
Definition setup pol t s u:=regs u 3%nat=regs s 6%nat /\ regs u 12%nat=regs s 2%nat mod 256 /\
 regs u 13%nat=regs s 1%nat /\ regs u 14%nat=regs s 8%nat /\ regs u 15%nat=regs s 9%nat /\ regs u 5%nat=regs s 5%nat /\
 match pol with Zip215=>regs u 4%nat=t-8 /\ regs u 7%nat=t /\ regs u 6%nat=regs s 7%nat
              | Dalek=>regs u 4%nat=t /\ regs u 1%nat=regs s 1%nat end.

Lemma raw pol bias s c t : regs s 4%nat=t -> 8<=t<2^64 -> word64(bias+candidate pol) ->
 exists u,run (length(path pol)) (ScalarBytes.fetch (o pol bias) (ScoreSetup.code pol))
  (State(Running 24) s c)=Some(State(Running(target pol bias-o pol bias)) u c,[event pol bias t (regs s 7%nat)]) /\ setup pol t s u.
Proof.
 intros SP Fit Target;destruct pol;eexists;split.
 - apply (InstructionRoute.checked _ _ _ (image Zip215)).
   cbn [path follow step cpu_state cf loc option_map push push_words regs set set_regs with_words mem put Nat.eqb app];rewrite SP.
   rewrite (word_fits (t-8)) by (unfold word64;lia).
   replace (o Zip215 bias+(46+Z.of_nat 5+(candidate Zip215-(ScoreSetup.callee Zip215+51)))) with (bias+candidate Zip215) by (unfold o;ring).
   rewrite (word_fits _ Target);reflexivity.
 - cbn [setup set set_regs with_words regs put Nat.eqb];repeat split;reflexivity.
 - apply (InstructionRoute.checked _ _ _ (image Dalek)).
   cbn [path follow step cpu_state cf loc option_map effective set set_regs with_words regs mem put Nat.eqb app];rewrite SP,!Z.add_0_r,(word_fits t ltac:(unfold word64;lia)).
   replace (target Dalek bias-o Dalek bias) with 44 by (unfold target,o;ring);reflexivity.
 - cbn [setup with_words regs put Nat.eqb];repeat split;try reflexivity;exact SP.
Qed.

Record ready pol bias e p q:Prop:=Ready {
 pc:ip q=target pol bias; writes:accounted e (writable e) q; words:well_formed(machine q);
 arguments:setup pol (ScoreFrame.buffer e) (machine p) (machine q);
 memory:mem(machine q)=commit (mem(machine p)) (event pol bias (ScoreFrame.buffer e) (regs(machine p) 7%nat));
 store_log:log q=log p++[event pol bias (ScoreFrame.buffer e) (regs(machine p) 7%nat)]
}.
Theorem checked pol bias e entry p : placement e -> loaded pol bias (mem e) (writable e) ->
 ScoreFrame.ready pol bias e entry p -> exists q,execute pol bias p=Some q /\ ready pol bias e p q.
Proof.
 intros P I F;set (t:=ScoreFrame.buffer e);destruct(stack_ok _ P) as [[Low High] _].
 pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)) as Al.
 assert (Fit:8<=t<2^64) by (unfold t,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia).
 destruct(raw pol bias (machine p) (carry p) t (ScoreFrame.stack _ _ _ _ _ F) Fit
    (mapped_word _ _ _ I _ _ (candidate_image pol) ltac:(destruct pol;vm_compute;reflexivity))) as [u [Run A]].
 pose proof(ScoreFrame.writes _ _ _ _ _ F) as Acc.
 destruct(mapped_now _ _ _ I _ _ _ Acc (ScoreSetup.image pol)) as [Map Sep].
 assert (Safe:confined (writable e) [event pol bias t (regs(machine p) 7%nat)]).
 { constructor;[intros x X;left;destruct pol;unfold touches,event in X;cbn [qword address size] in X;
    unfold span,t,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia|constructor]. }
 destruct(at_segment _ _ p _ _ _ 24 _ _ Acc (ScoreFrame.pc _ _ _ _ _ F) Map Sep Run Safe) as [Next Paid].
 eexists;split;[exact Next|constructor].
 - cbn [LinkedRun.finish ip];unfold absolute;cbn [loc];unfold o;ring.
 - exact Paid.
 - exact (segment_wf _ _ _ _ _ (ScoreFrame.words _ _ _ _ _ F) Next).
 - exact A.
 - exact (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Run)).
 - reflexivity.
Qed.

Definition from_call pol bias p:=bind (ScoreFrame.enter pol bias p) (execute pol bias).
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record reached pol bias pc0 e h r p q:Prop:=Reached {
 caller:ScoreCall.entered pol bias pc0 e h r p;
 prologue:exists f,ScoreFrame.enter pol bias p=Some f /\ ScoreFrame.ready pol bias e p f /\
              execute pol bias f=Some q /\ ready pol bias e f q
}.
Theorem from_entry pol bias pc0 e h r p : placement e -> loaded pol bias (mem e) (writable e) ->
 ScoreCall.entered pol bias pc0 e h r p -> exists q,from_call pol bias p=Some q /\ reached pol bias pc0 e h r p q.
Proof.
 intros P I E;destruct(ScoreFrame.checked _ _ _ _ _ _ _ P I E) as [f [F Frame]].
 destruct(checked _ _ _ _ _ P I Frame) as [q [Run Q]].
 exists q;split;[unfold from_call;rewrite F;exact Run|constructor;[exact E|exists f;auto]].
Qed.
Lemma accounted pol bias pc0 e h r p q : reached pol bias pc0 e h r p q -> LinkedRun.accounted e (writable e) q.
Proof. intros [_ [f [_ [_ [_ S]]]]];exact (writes _ _ _ _ _ S). Qed.
End Iteration.
