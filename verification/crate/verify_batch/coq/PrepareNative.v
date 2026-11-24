From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.WordSemantics execution.WordBounds
 execution.StoreInstructions execution.ScalarBytes execution.MappedFetch execution.InstructionRoute
 memory.ByteMemory memory.FlatMemory memory.WriteTrace memory.MemoryGeometry.
From Machine Require isa.VectorMoves.
From Ed25519Simd.PrepareChunk Require CommonBytes StrictBytes.
From Ed25519Simd.SignatureScalar Require ObjectBytes OrderBytes Program Audit Object.
Import ListNotations. Local Open Scope Z_scope.

Definition common := CommonBytes.address.
Definition strict := StrictBytes.address.
Definition scalar := SignatureScalar.ObjectBytes.address.
Definition strict_path : list line :=
 [(0,1%nat,SaveG 3);(1,3%nat,CopyG 3 1);(4,5%nat,CallRelative (common-(strict+9)))].
Definition saves : list line :=
 [(0,1%nat,SaveG 3);(1,2%nat,SaveG 12);(3,2%nat,SaveG 13);
  (5,2%nat,SaveG 14);(7,2%nat,SaveG 15)].
Definition assign : list line :=
 [(9,4%nat,Sub64 4 64);(13,3%nat,CopyG 3 7);(16,3%nat,CopyG 12 2);
  (19,3%nat,CopyG 13 1);(22,3%nat,CopyG 15 6)].
Definition pointers : list line :=
 [(25,5%nat,Imm32 0 32);(30,6%nat,BroadcastG 0 0);(36,7%nat,AddVectorMem 0 0 (Address 6 None 64));
  (43,7%nat,VectorMove (VectorMoves.Output 0 4 0))].
Definition dispatch : list line :=
 [(50,7%nat,LeaG 7 (Address 3 None 512));(57,3%nat,CopyG 6 4);
  (60,5%nat,CallRelative (scalar-(common+65)))].
Lemma strict_linked : linked StrictBytes.symbol_bytes strict_path.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Lemma saves_linked : linked CommonBytes.symbol_bytes saves.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Lemma assign_linked : linked CommonBytes.symbol_bytes assign.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Lemma pointers_linked : linked CommonBytes.symbol_bytes pointers.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Lemma dispatch_linked : linked CommonBytes.symbol_bytes dispatch.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition stack_range top below x := top-below<=x<top.
Definition at_pc ip := State (Running ip).
Definition words_fit top := 128<=top<2^64.

Local Ltac simplify_cpu :=
 cbn [at_pc loc cpu_state cf caller_stores step regs vectors mem with_zf set set_regs with_words Instructions.put
      push push_words apply_stack caller_step next_pc encoding stack_step result_regs result_mem
      target_ip store_word fst snd Nat.eqb effective].
Local Ltac normalize := repeat match goal with |-context[word ?x]=>rewrite (word_fits x ltac:(unfold word64, words_fit in *;lia)) end.

Lemma strict_dispatch slide s carry top :
 regs s 4%nat=top -> words_fit top -> word64 (slide+common) ->
 exists t ws, MappedFetch.run 3 (ScalarBytes.fetch (slide+strict) StrictBytes.symbol_bytes)
    (at_pc 0 s carry)=Some(t,ws) /\
 loc t=Running (common-strict) /\ regs (cpu_state t) 4%nat=top-16 /\
 regs (cpu_state t) 7%nat=regs s 7%nat /\ regs (cpu_state t) 6%nat=regs s 6%nat /\
 read_word (mem (cpu_state t)) (top-16)=word(slide+strict+9) /\
 confined (stack_range top 16) ws.
Proof.
 intros SP Fit PC.
 lazymatch goal with |- exists t ws, _ => do 2 eexists end;split.
 - apply (checked _ _ _ strict_linked);reflexivity.
 - cbn [strict_path follow step loc cpu_state cf option_map app];simplify_cpu.
   unfold strict,common in *;cbn [StrictBytes.address CommonBytes.address] in *.
   normalize.
   rewrite SP. normalize.
   split;[f_equal;unfold common,strict,CommonBytes.address,StrictBytes.address;lia|].
   split;[lia|]. split;[reflexivity|]. split;[reflexivity|]. split.
   + apply read_word_encoded;intros k K;unfold store_word;replace (top-16+k) with (top-8-8+k) by ring;
       apply write_at,K.
   + constructor;[|constructor;[|constructor]];intros x X;
       unfold stack_range,touches in *;cbn [caller_stores qword address size] in X;
       simplify_cpu;rewrite ?SP in X;repeat rewrite word_fits in X by (unfold words_fit,word64 in *;lia);lia.
Qed.

Definition common_post slide top s t :=
 loc t=Running (scalar-common) /\ regs (cpu_state t) 4%nat=top-112 /\
 regs (cpu_state t) 6%nat=top-104 /\ regs (cpu_state t) 7%nat=word(regs s 7%nat+512) /\
 read_word (mem (cpu_state t)) (top-112)=word(slide+common+65).

Definition common_fetch slide := ScalarBytes.fetch (slide+common) CommonBytes.symbol_bytes.

Lemma saved slide s carry top : regs s 4%nat=top -> words_fit top ->
 exists u ws, MappedFetch.run 5 (common_fetch slide) (at_pc 0 s carry)=Some(at_pc 9 u carry,ws) /\
 regs u 4%nat=top-40 /\ regs u 7%nat=regs s 7%nat /\ regs u 6%nat=regs s 6%nat /\
 confined (stack_range top 40) ws.
Proof.
 intros SP Fit;do 2 eexists;split;[apply (checked _ _ _ saves_linked);reflexivity|].
 simplify_cpu;rewrite SP;normalize.
 split;[lia|]. split;[reflexivity|]. split;[reflexivity|].
 cbn [app]. repeat apply Forall_cons;try apply Forall_nil.
 all: intros x X;unfold stack_range,touches in *;cbn [qword address size] in X;lia.
Qed.

Lemma assigned slide s carry top : regs s 4%nat=top-40 -> words_fit top ->
 exists u c,MappedFetch.run 5 (common_fetch slide) (at_pc 9 s carry)=Some(at_pc 25 u c,[]) /\
 regs u 4%nat=top-104 /\ regs u 3%nat=regs s 7%nat /\ regs u 6%nat=regs s 6%nat /\ mem u=mem s.
Proof.
 intros SP Fit;do 2 eexists;split;[apply (checked _ _ _ assign_linked);reflexivity|].
 simplify_cpu;rewrite SP;normalize;repeat split;lia.
Qed.

Definition signed_pointer s j := word (32+read_word (mem s) (effective s (Address 6 None 64)+8*Z.of_nat j)).
Lemma stored slide s c top : regs s 4%nat=top-104 -> words_fit top ->
 exists u ws,MappedFetch.run 4 (common_fetch slide) (at_pc 25 s c)=Some(at_pc 50 u c,ws) /\
 regs u 4%nat=top-104 /\ regs u 3%nat=regs s 3%nat /\
 (forall j,(j<8)%nat -> read_word (mem u) (top-104+8*Z.of_nat j)=signed_pointer s j) /\
 confined (stack_range top 112) ws.
Proof.
 intros SP Fit;do 2 eexists;split;[apply (checked _ _ _ pointers_linked);reflexivity|].
 simplify_cpu;rewrite SP, Z.add_0_r;normalize.
 split;[reflexivity|]. split;[reflexivity|]. split.
 - intros j J. apply write_read_vector;[exact J|apply mod64_word].
 - constructor;[|constructor]. intros x X;change (top-104<=x<top-104+64) in X;unfold stack_range;lia.
Qed.

Lemma dispatched slide s c top : regs s 4%nat=top-104 -> words_fit top -> word64(slide+scalar) ->
 exists t ws,MappedFetch.run 3 (common_fetch slide) (at_pc 50 s c)=Some(t,ws) /\
 loc t=Running (scalar-common) /\ regs (cpu_state t) 4%nat=top-112 /\
 regs (cpu_state t) 6%nat=top-104 /\ regs (cpu_state t) 7%nat=word(regs s 3%nat+512) /\
 read_word (mem (cpu_state t)) (top-112)=word(slide+common+65) /\
 (forall j,read_word (mem (cpu_state t)) (top-104+8*Z.of_nat j)=read_word (mem s) (top-104+8*Z.of_nat j)) /\
 confined (stack_range top 112) ws.
Proof.
 intros SP Fit PC;do 2 eexists;split;[apply (checked _ _ _ dispatch_linked);reflexivity|].
 simplify_cpu;rewrite SP,!Z.add_0_r;normalize.
 split;[f_equal;replace (slide+common+(60+Z.of_nat 5+(scalar-(common+65)))) with (slide+scalar) by ring;
    rewrite ?(word_fits _ PC);ring|].
 replace (top-104-8) with (top-112) by ring.
 split;[reflexivity|]. split;[reflexivity|]. split;[reflexivity|]. split.
 - change (read_word (store_word (mem s) (top-112) (slide+common+65)) (top-112) = word(slide+common+65)).
   apply read_word_encoded;intros k K;apply write_at,K.
 - split;[intro j;apply read_other_word;unfold disjoint;lia|].
   constructor;[|constructor];intros x X;change (top-112<=x<top-112+8) in X;unfold stack_range;lia.
Qed.

Definition ptr_row s j := regs s 6%nat+64+8*Z.of_nat j.
Lemma common_dispatch slide s carry top :
 regs s 4%nat=top -> words_fit top -> word64 (slide+scalar) ->
 fits64 (regs s 6%nat) 128 -> disjoint (top-40) 40 (regs s 6%nat+64) 64 ->
 exists t ws, MappedFetch.run 17 (common_fetch slide) (at_pc 0 s carry)=Some(t,ws) /\
 common_post slide top s t /\ confined (stack_range top 112) ws /\
 forall j,(j<8)%nat -> read_word (mem (cpu_state t)) (top-104+8*Z.of_nat j)=
 word(32+read_word (mem s) (ptr_row s j)).
Proof.
 intros SP Fit PC Table Separate.
 destruct (saved slide s carry top SP Fit) as [v [head [S [VSP [DI [SI H]]]]]].
 destruct (assigned slide v carry top VSP Fit) as [a [ca [A [ASP [BX [RSI Mem]]]]]].
 destruct (stored slide a ca top ASP Fit) as [b [stores [B [BSP [RBX [Ptrs W]]]]]].
 destruct (dispatched slide b ca top BSP Fit PC) as [t [tail [T [IP [Top [R6 [R7 [Ret [Keep Safe]]]]]]]]].
 pose proof(run_append _ _ _ _ _ S _ _ _ A) as First.
 pose proof(run_append _ _ _ _ _ First _ _ _ B) as Second.
 pose proof(run_append _ _ _ _ _ Second _ _ _ T) as All.
 exists t,(((head++[])++stores)++tail);split;[exact All|].
 split;[unfold common_post;rewrite R7,RBX,BX,DI;auto|]. split.
 - rewrite app_nil_r;unfold confined;rewrite !Forall_app;repeat split;auto.
   eapply Forall_impl;[|exact H]. unfold permits,stack_range;intros w Allowed x X;specialize (Allowed x X);lia.
 - intros j J;rewrite Keep,Ptrs by exact J.
   unfold signed_pointer,ptr_row;cbn [effective];rewrite Mem,RSI,SI,Z.add_0_r,(word_fits (regs s 6%nat+64)) by
     (destruct Table;unfold word64;lia).
   f_equal;f_equal.
   pose proof (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ S)) as M.
   change (mem v=WriteTrace.replay (mem s) head) in M;rewrite M.
   apply preserved_read with (outside:=fun x=>~stack_range top 40 x).
   + exact (WriteTrace.frame _ _ H (mem s)).
   + intros k K;change (0<=k<8) in K;unfold stack_range,disjoint in *;lia.
Qed.
