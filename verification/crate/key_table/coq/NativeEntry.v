From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions isa.QwordRegister execution.WordSemantics execution.WordBounds
 execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.ScalarWords execution.StoreInstructions
 execution.MappedFetch execution.InstructionRoute execution.CursorSegment abi.RegisterSpill memory.Alignment memory.ByteMemory memory.WriteTrace.
From Ed25519Simd.KeyTable Require Frame.
From Machine Require abi.FramePointer.
Import ListNotations. Local Open Scope Z_scope.

Definition saves:=FramePointer.pushes.
Definition allocate:list line:=[(13,4%nat,AndImmediate 4 (-64));(17,7%nat,Sub64 4 960);
 (24,3%nat,CopyG 12 7);(27,7%nat,LeaG 13 (Address 6 None 1280));(34,3%nat,CopyG 14 13);
 (37,2%nat,Copy32 3 2);(39,3%nat,CopyG 0 13);(42,2%nat,Copy32 1 2);
 (44,6%nat,QwordOp(Alu(0%nat,Xor 0 0)))].
Definition image text:=linked text saves /\ linked text allocate.

Definition save_area sp x:=sp-48<=x<sp.
Lemma save text o s c sp : image text -> regs s 4%nat=sp -> 1200<=sp<2^64 ->
 exists t ws,run 7 (ScalarBytes.fetch o text) (State(Running 0) s c)=Some(State(Running 13) t c,ws) /\
 confined (save_area sp) ws /\ mem t=spill (regs s) (mem s) sp Frame.saved_regs /\
 regs t 4%nat=sp-48 /\ regs t 5%nat=sp-8 /\ regs t 7%nat=regs s 7%nat /\
 regs t 6%nat=regs s 6%nat /\ regs t 2%nat=regs s 2%nat.
Proof.
 intros Code SP Fit;destruct(FramePointer.save text o s c sp (proj1 Code) SP ltac:(lia)) as [t [R [Stack [BP G]]]].
 exists t,(FramePointer.stores o sp (regs s));split;[exact R|split;[apply FramePointer.confined|]].
 split.
 - etransitivity;[exact (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R))|].
   cbn [FramePointer.stores replay fold_left spill Frame.saved_regs KeyTable.Frame.saves];
   replace (sp-8-8) with (sp-16) by ring;replace (sp-16-8) with (sp-24) by ring;
   replace (sp-24-8) with (sp-32) by ring;replace (sp-32-8) with (sp-40) by ring;
   replace (sp-40-8) with (sp-48) by ring;reflexivity.
 - split;[exact Stack|split;[exact BP|repeat apply conj;apply G;discriminate]].
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

Lemma setup text o s c sp pt dst : image text -> 1200<=sp<2^64 -> word64(dst+1280) ->
 regs s 4%nat=sp-48 -> regs s 5%nat=sp-8 -> regs s 7%nat=pt -> regs s 6%nat=dst -> regs s 2%nat=8 ->
 exists t cf,run 9 (ScalarBytes.fetch o text) (State(Running 13) s c)=Some(State(Running 50) t cf,[]) /\
 ready sp pt dst t /\ mem t=mem s.
Proof.
 intros Code Fit D SP BP DI SI DX;do 2 eexists;split;[apply (InstructionRoute.checked _ _ _ (proj2 Code));reflexivity|].
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

Definition execute base text:=segment base text 16.

Record entered root allowed base sp pt dst p q : Prop := Entered {
 address:ip q=base+50;
 valid:valid_cursor root allowed q;
 arguments:ready sp pt dst (machine q);
 memory_after:mem(machine q)=spill (regs(machine p)) (mem(machine p)) sp Frame.saved_regs;
 history:StoreHistory.extends (save_area sp) p q
}.

Theorem checked root allowed base text sp pt dst p : image text ->
 available root allowed base text -> valid_cursor root allowed p -> ip p=base ->
 1200<=sp<2^64 -> word64(dst+1280) -> (forall x,save_area sp x -> allowed x) ->
 regs(machine p) 4%nat=sp -> regs(machine p) 7%nat=pt ->
 regs(machine p) 6%nat=dst -> regs(machine p) 2%nat=8 ->
 exists q,execute base text p=Some q /\ entered root allowed base sp pt dst p q.
Proof.
 intros Code Image V PC Fit D Region SP DI SI DX.
 destruct(save text base (machine p) (carry p) sp Code SP Fit)
   as [a [ws [A [Safe [M [SA [BP [AD [AS AX]]]]]]]]].
 destruct(setup text base a (carry p) sp pt dst Code Fit D SA BP
   ltac:(congruence) ltac:(congruence) ltac:(congruence)) as [b [c [B [Args Mb]]]].
 pose proof(run_append _ _ _ _ _ A _ _ _ B) as Run;rewrite app_nil_r in Run.
 destruct(CursorSegment.checked root allowed (save_area sp) base text 16 p 0 _ _
   Image Region V ltac:(now rewrite Z.add_0_r) Run Safe) as [Step [Valid History]].
 eexists;split;[exact Step|constructor];[reflexivity|exact Valid|exact Args|exact (eq_trans Mb M)|exact History].
Qed.
