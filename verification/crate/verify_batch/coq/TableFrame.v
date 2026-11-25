From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions isa.QwordRegister execution.WordSemantics execution.WordBounds
 execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.ScalarWords execution.StoreInstructions
 execution.MappedFetch execution.InstructionRoute memory.Alignment memory.ByteMemory memory.WriteTrace.
From Ed25519Simd.KeyTable Require Frame ObjectBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require TableEntry.
Import ListNotations. Local Open Scope Z_scope.

Definition text:=KeyTable.ObjectBytes.symbol_bytes.
Definition base bias:=bias+TableEntry.origin.
Definition saved_regs:=5%nat::KeyTable.Frame.saves.
Definition saves:list line:=[(0,1%nat,SaveG 5);(1,3%nat,CopyG 5 4);
 (4,1%nat,SaveG 3);(5,2%nat,SaveG 12);(7,2%nat,SaveG 13);(9,2%nat,SaveG 14);(11,2%nat,SaveG 15)].
Definition allocate:list line:=[(13,4%nat,AndImmediate 4 (-64));(17,7%nat,Sub64 4 960);
 (24,3%nat,CopyG 12 7);(27,7%nat,LeaG 13 (Address 6 None 1280));(34,3%nat,CopyG 14 13);
 (37,2%nat,Copy32 3 2);(39,3%nat,CopyG 0 13);(42,2%nat,Copy32 1 2);
 (44,6%nat,QwordOp(Alu(0%nat,Xor 0 0)))].
Lemma image:linked text saves /\ linked text allocate.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Definition save_area sp x:=sp-48<=x<sp.
Lemma save o s c sp : regs s 4%nat=sp -> 1200<=sp<2^64 ->
 exists t ws,run 7 (ScalarBytes.fetch o text) (State(Running 0) s c)=Some(State(Running 13) t c,ws) /\
 confined (save_area sp) ws /\ mem t=spill (regs s) (mem s) sp saved_regs /\
 regs t 4%nat=sp-48 /\ regs t 5%nat=sp-8 /\ regs t 7%nat=regs s 7%nat /\
 regs t 6%nat=regs s 6%nat /\ regs t 2%nat=regs s 2%nat.
Proof.
 intros SP Fit;do 2 eexists;split;[apply (InstructionRoute.checked _ _ _ (proj1 image));reflexivity|].
 cbn [saves follow loc cf cpu_state step option_map app snd caller_stores caller_step apply_stack stack_step
   result_regs result_mem target_ip with_words push push_words set set_regs regs mem put Nat.eqb
   spill saved_regs KeyTable.Frame.saves];rewrite SP.
 repeat match goal with |-context[word ?x]=>rewrite (word_fits x ltac:(unfold word64 in *;lia)) end.
 split;[repeat apply Forall_cons;try apply Forall_nil;intros x X;unfold save_area,touches in *;
    cbn [qword WriteTrace.address WriteTrace.size] in X;lia|].
 repeat split;reflexivity || lia.
Qed.

Record ready sp pt dst s:Prop:=Ready {
 stack:regs s 4%nat=KeyTable.Frame.staging sp;
 fp:regs s 5%nat=sp-8;
 source:regs s 12%nat=pt;
 positive:regs s 13%nat=dst+1280;
 negative:regs s 14%nat=dst+1280;
 count:regs s 3%nat=8;
 pointer:regs s 0%nat=dst+1280;
 remaining:regs s 1%nat=8;
 zero:forall j,vectors s j 0%nat=0
}.

Lemma setup o s c sp pt dst : 1200<=sp<2^64 -> word64(dst+1280) ->
 regs s 4%nat=sp-48 -> regs s 5%nat=sp-8 -> regs s 7%nat=pt -> regs s 6%nat=dst -> regs s 2%nat=8 ->
 exists t cf,run 9 (ScalarBytes.fetch o text) (State(Running 13) s c)=Some(State(Running 50) t cf,[]) /\
 ready sp pt dst t /\ mem t=mem s.
Proof.
 intros Fit D SP BP DI SI DX;do 2 eexists;split;[apply (InstructionRoute.checked _ _ _ (proj2 image));reflexivity|].
 cbn [allocate follow loc cf cpu_state step option_map qword_op effective vector_dest with_zf set set_regs regs mem
   vectors Nat.eqb put];split;[constructor|reflexivity].
 all: cbn [vector_dest with_zf set set_regs regs vectors put Nat.eqb];rewrite ?SP,?BP,?DI,?SI,?DX,?and_rsp_64,?Z.add_0_r,?(word_fits _ D).
 - unfold KeyTable.Frame.staging,KeyTable.Frame.align64,KeyTable.Frame.allocation;change KeyTable.Frame.saved_size with 48.
   pose proof(Z.mod_pos_bound (sp-48) 64 ltac:(lia));change (word 960) with 960.
   repeat match goal with |-context[word ?x]=>rewrite (word_fits x ltac:(unfold word64;lia)) end;reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - intro j;unfold bits,Logic.vpxorq;rewrite Z.lxor_nilpotent;reflexivity.
Qed.

Definition enter bias:=segment (base bias) text 16.
Record initialized pol bias e p q:Prop:=Initialized {
 address:ip q=base bias+50;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 arguments:ready (TableEntry.frame pol e) (TableEntry.point e) (TableEntry.tables e) (machine q);
 memory_after:mem(machine q)=spill (regs(machine p)) (mem(machine p)) (TableEntry.frame pol e) saved_regs
}.

Theorem checked pol bias e caller p : placement e -> loaded pol bias (mem e) (writable e) ->
 TableEntry.entry pol bias e caller p -> exists q,enter bias p=Some q /\ initialized pol bias e p q.
Proof.
 intros P I E;set (o:=base bias);set (t:=TableEntry.frame pol e);set (s:=machine p).
 destruct(TableEntry.arguments _ _ _ _ _ E) as [SP [DI [SI DX]]];fold t s in SP,DI,SI,DX.
 destruct(stack_ok _ P) as [[L H] _];destruct(scratch_ok _ P) as [[DL DH] _].
 assert (Stack:Return.sp e-1200<=t<Return.sp e-1000) by (unfold t,TableEntry.frame,common_top,Rows.frame,Return.sp;destruct pol;lia).
 assert (Fit:1200<=t<2^64) by lia.
 destruct(save o s (LinkedRun.carry p) t SP Fit) as [a [ws [A [Safe [M [SA [BP [AD [AS AX]]]]]]]]].
 destruct(setup o a (LinkedRun.carry p) t (TableEntry.point e) (TableEntry.tables e) Fit
  ltac:(unfold TableEntry.tables,word64;lia) SA BP ltac:(congruence) ltac:(congruence) ltac:(congruence))
  as [b [c [B [Args Mb]]]].
 pose proof(run_append _ _ _ _ _ A _ _ _ B) as Run;rewrite app_nil_r in Run.
 pose proof(TableEntry.writes _ _ _ _ _ E) as Acc;destruct(mapped_now _ _ _ I _ _ _ Acc (TableEntry.image pol)) as [Map Sep].
 assert (Ok:confined (writable e) ws).
 { eapply Forall_impl;[|exact Safe];intros w W x X;specialize(W x X);left;unfold save_area,span in *;lia. }
 destruct(at_segment _ _ p o text 16 0 _ _ Acc ltac:(rewrite Z.add_0_r;apply (TableEntry.address _ _ _ _ _ E)) Map Sep Run Ok) as [Next Paid].
 eexists;split;[exact Next|constructor];[reflexivity|exact Paid|exact (segment_wf _ _ _ _ _ (TableEntry.words _ _ _ _ _ E) Next)|exact Args|].
 exact (eq_trans Mb M).
Qed.
