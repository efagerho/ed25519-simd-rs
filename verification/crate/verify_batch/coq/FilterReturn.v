From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require FilterLoad.
Import ListNotations. Local Open Scope Z_scope.

Definition path:list line:=[(543,4%nat,Add64 4 8);(547,3%nat,ZeroUpper);(550,1%nat,Ret)].
Lemma bytes:linked FilterLoad.text path.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute bias:=segment (bias+FilterLoad.site) FilterLoad.text 3.
Record result bias e p q:Prop:=Result {
 pc:ip q=StrictFilterCall.link bias; writes:accounted e (writable e) q; words:well_formed(machine q);
 stack:regs(machine q) 4%nat=StrictFilterCall.slot e+8;
 kept:forall r,r<>4%nat -> regs(machine q) r=regs(machine p) r;
 memory_after:mem(machine q)=mem(machine p); history:log q=log p
}.
Theorem checked bias e p : placement e -> loaded Dalek bias (mem e) (writable e) -> ip p=bias+FilterLoad.site+543 ->
 accounted e (writable e) p -> well_formed(machine p) -> regs(machine p) 4%nat=StrictFilterCall.slot e-8 ->
 read_word (mem(machine p)) (StrictFilterCall.slot e)=StrictFilterCall.link bias ->
 exists q,execute bias p=Some q /\ result bias e p q.
Proof.
 intros P I PC Acc W SP Back;set (o:=bias+FilterLoad.site) in *;set (t:=StrictFilterCall.slot e) in *.
 destruct(stack_ok _ P) as [[L H] _];assert (Room:0<=t-8 /\ t+8<2^64) by (unfold t,StrictFilterCall.slot,common_top,Rows.frame,sp in *;lia).
 assert (Raw:exists last,run 3 (ScalarBytes.fetch o FilterLoad.text) (State(Running 543) (machine p) (LinkedRun.carry p))=Some(last,[]) /\
    loc last=Returned(StrictFilterCall.link bias) /\ regs(cpu_state last) 4%nat=t+8 /\
    mem(cpu_state last)=mem(machine p) /\ forall r,r<>4%nat -> regs(cpu_state last) r=regs(machine p) r).
 { eexists;split;[apply (InstructionRoute.checked _ _ _ bytes);reflexivity|].
   cbn [path follow loc cpu_state cf ScalarBytes.step option_map caller_step stack_step result_regs result_mem
    target_ip advance_rsp stack_top apply_stack with_words regs set set_regs with_zf mem put Nat.eqb].
   unfold advance_rsp,stack_top,put;cbn [Nat.eqb];rewrite SP.
   repeat match goal with |-context[word ?x]=>rewrite (word_fits x ltac:(unfold word64;lia)) end.
   replace (t-8+8) with t by ring;rewrite Back,word_fits by (rewrite <-Back;apply read_word_bound,W).
   split;[reflexivity|split;[reflexivity|split;[reflexivity|]]].
   intros r N;destruct r as [|[|[|[|[|r]]]]];congruence. }
 destruct Raw as [last [Run [IP [Stack [Mem Reg]]]]];destruct(mapped_now _ _ _ I _ _ _ Acc StrictFilterCall.in_filter) as [Map Sep].
 destruct(at_segment _ _ p o FilterLoad.text 3 543 _ _ Acc PC Map Sep Run (Forall_nil _)) as [End Paid].
 eexists;split;[exact End|constructor];[cbn [LinkedRun.finish ip];unfold absolute;now rewrite IP|exact Paid|exact (segment_wf _ _ _ _ _ W End)|
    exact Stack|exact Reg|exact Mem|apply app_nil_r].
Qed.
