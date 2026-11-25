From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls
 execution.LinkedRun execution.ScalarBytes execution.ScalarWords execution.InstructionRoute execution.MappedFetch
 memory.ByteMemory memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require TableEntry TableFrame TableIdentity.
Import ListNotations. Local Open Scope Z_scope.

Definition begin_digit:list line:=[(104,6%nat,Imm32 15 1)].
Definition move:list line:=[(110,7%nat,Add64 13 160);(117,7%nat,Sub64 14 160)].
Lemma image:linked TableFrame.text begin_digit /\ linked TableFrame.text move.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Definition pos e d:=TableIdentity.first e+160*d.
Definition neg e d:=TableIdentity.first e-160*d.
Record pointers pol e digit s:Prop:=Pointers {
 stack:regs s 4%nat=KeyTable.Frame.staging(TableEntry.frame pol e);
 source:regs s 12%nat=TableEntry.point e;
 positive:regs s 13%nat=pos e digit;
 negative:regs s 14%nat=neg e digit;
 count:regs s 3%nat=8;
 multiple:regs s 15%nat=digit;
 frame_pointer:regs s 5%nat=TableEntry.frame pol e-8
}.

Definition start bias:=segment (TableFrame.base bias) TableFrame.text 3.
Definition advance bias:=segment (TableFrame.base bias) TableFrame.text 2.

Lemma shifted o s c a b : word64 a -> word64 b -> word64(a+160) -> word64(b-160) ->
 regs s 13%nat=a -> regs s 14%nat=b ->
 exists t f,run 2 (ScalarBytes.fetch o TableFrame.text) (State(Running 110) s c)=Some(State(Running 124) t f,[]) /\
 regs t=put (put (regs s) 13 (a+160)) 14 (b-160) /\ mem t=mem s /\ vectors t=vectors s.
Proof.
 intros A B AA BB P N;do 2 eexists;split;[apply (InstructionRoute.checked _ _ _ (proj2 image));reflexivity|].
 cbn [move follow loc cpu_state cf step option_map regs set with_zf set_regs put Nat.eqb];rewrite P,N.
 change (word 160) with 160;rewrite (word_fits _ A),(word_fits _ B),(word_fits _ AA),(word_fits _ BB);auto.
Qed.

Record positioned pol bias e digit p q : Prop:=Positioned {
 address:ip q=TableFrame.base bias+124;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 arguments:pointers pol e digit (machine q);
 flat:mem(machine q)=mem(machine p);
 vectors_after:vectors(machine q)=vectors(machine p);
 journal:log q=log p
}.
Theorem first pol bias e entry callee p : placement e -> loaded pol bias (mem e) (writable e) ->
 TableFrame.initialized pol bias e entry callee -> TableIdentity.filled pol bias e callee p ->
 exists q,start bias p=Some q /\ positioned pol bias e 1 p q.
Proof.
 intros P I Frame Identity;set (s:=machine p);set (o:=TableFrame.base bias).
 pose proof(TableFrame.arguments _ _ _ _ _ Frame) as Args.
 pose proof(TableIdentity.registers _ _ _ _ _ Identity) as Static;fold s in Static.
 assert (R13:regs s 13%nat=TableIdentity.first e) by (rewrite Static by discriminate;exact (TableFrame.positive _ _ _ _ Args)).
 assert (R14:regs s 14%nat=TableIdentity.first e) by (rewrite Static by discriminate;exact (TableFrame.negative _ _ _ _ Args)).
 set (a:=TableIdentity.first e) in *;destruct(scratch_ok _ P) as [[Lo Hi] _].
 assert (Bound:forall k,-160<=k<=160 -> word64(a+k)) by (unfold a,TableIdentity.first,TableEntry.tables,word64;lia).
 assert (Fit:word64 a) by (specialize(Bound 0 ltac:(lia));now rewrite Z.add_0_r in Bound).
 set (b:=set s 15 1);assert (Begin:run 1 (ScalarBytes.fetch o TableFrame.text) (State(Running 104) s (LinkedRun.carry p))=
  Some(State(Running 110) b (LinkedRun.carry p),[])) by (apply (InstructionRoute.checked _ _ _ (proj1 image));reflexivity).
 destruct(shifted o b (LinkedRun.carry p) a a Fit Fit (Bound 160 ltac:(lia)) (Bound (-160) ltac:(lia)) R13 R14)
  as [t [c [Move [G [M V]]]]].
 pose proof(run_append _ _ _ _ _ Begin _ _ _ Move) as Run.
 pose proof(TableIdentity.writes _ _ _ _ _ Identity) as Acc;destruct(mapped_now _ _ _ I _ _ _ Acc (TableEntry.image pol)) as [Map Sep].
 destruct(at_segment _ _ p o TableFrame.text 3 104 _ _ Acc (TableIdentity.address _ _ _ _ _ Identity) Map Sep Run (Forall_nil _)) as [Next Paid].
 eexists;split;[exact Next|constructor].
 - reflexivity.
 - exact Paid.
 - exact (segment_wf _ _ _ _ _ (TableIdentity.words _ _ _ _ _ Identity) Next).
 - change (pointers pol e 1 t);constructor;rewrite G;cbn [b set set_regs regs put Nat.eqb].
   + exact (TableIdentity.stack_base _ _ _ _ _ Identity).
   + rewrite Static by discriminate;exact (TableFrame.source _ _ _ _ Args).
   + unfold pos;fold a;ring.
   + unfold neg;fold a;ring.
   + rewrite Static by discriminate;exact (TableFrame.count _ _ _ _ Args).
   + reflexivity.
   + rewrite Static by discriminate;exact (TableFrame.fp _ _ _ _ Args).
 - exact M.
 - exact V.
 - apply app_nil_r.
Qed.
