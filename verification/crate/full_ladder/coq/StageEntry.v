From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.MappedFetch execution.InstructionRoute execution.ScalarBytes execution.ScalarWords execution.StoreInstructions
 memory.Alignment memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Machine Require abi.FramePointer.
From Ed25519Simd.FullLadder Require Import LinkedBytes.
Import ListNotations. Local Open Scope Z_scope.

Definition base top:=top-64-top mod 64-3520.
Definition own:list line:=[(13,2%nat,SaveG 8);(15,2%nat,SaveG 9)].
Definition setup:list line:=[(17,4%nat,AndImmediate 4 (-64));(21,7%nat,Sub64 4 3520);
 (28,3%nat,CopyG 3 7);(31,3%nat,CopyG 12 6);(34,3%nat,CopyG 13 2);(37,3%nat,CopyG 14 1);
 (40,3%nat,CopyG 7 4);(43,6%nat,Imm32 9 31);(49,5%nat,CallRelative (stage_pc-(entry_pc+54)))].
Lemma image:linked symbol_bytes FramePointer.pushes /\ linked symbol_bytes own /\ linked symbol_bytes setup.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Definition spill o top s:=[qword (word(o+13)) (top-56) (regs s 8%nat);qword (word(o+15)) (top-64) (regs s 9%nat)].
Definition call_store o top:=qword (word(o+49)) (base top-8) (o+54).
Definition stores o top s:=FramePointer.stores o top (regs s)++spill o top s++[call_store o top].

Lemma push_args o top s c : regs s 4%nat=top-48 -> 64<=top<2^64 -> exists v,
 run 2 (ScalarBytes.fetch o symbol_bytes) (State(Running 13) s c)=Some(State(Running 17) v c,spill o top s) /\
 regs v 4%nat=top-64 /\ forall g,g<>4%nat -> regs v g=regs s g.
Proof.
 intros SP Range;eexists;split.
 - apply (InstructionRoute.checked _ _ _ (proj1(proj2 image)));cbn [own follow loc cpu_state cf step app option_map
   caller_stores caller_step apply_stack stack_step push_words result_regs result_mem target_ip snd with_words put mem regs Nat.eqb].
   rewrite SP;replace (top-48-8) with (top-56) by ring;replace (top-56-8) with (top-64) by ring.
   repeat match goal with |-context[word ?x]=>rewrite (word_fits x ltac:(unfold word64;lia)) end;
   replace (top-56-8) with (top-64) by ring;reflexivity.
 - split;[reflexivity|intros g N].
   change (put (put (regs s) 4 (top-56)) 4 (top-64) g=regs s g);unfold put;destruct(Nat.eqb_spec 4 g);congruence.
Qed.

Definition arguments top s u:=regs u 4%nat=base top-8 /\ regs u 7%nat=base top /\
 regs u 6%nat=regs s 6%nat /\ regs u 2%nat=regs s 2%nat /\ regs u 1%nat=regs s 1%nat /\
 regs u 8%nat=regs s 8%nat /\ regs u 9%nat=31 /\ regs u 3%nat=regs s 7%nat /\
 regs u 12%nat=regs s 6%nat /\ regs u 13%nat=regs s 2%nat /\ regs u 14%nat=regs s 1%nat.
Lemma first_call slide top s c : regs s 4%nat=top-64 -> 5032<=top<2^64 -> word64(slide+stage_pc) ->
 let o:=slide+entry_pc in exists u k,run 9 (ScalarBytes.fetch o symbol_bytes) (State(Running 17) s c)=
 Some(State(Running(stage_pc-entry_pc)) u k,[call_store o top]) /\ arguments top s u /\ regs u 5%nat=regs s 5%nat.
Proof.
 intros SP Fit Dest o;do 2 eexists;split.
 - apply (InstructionRoute.checked _ _ _ (proj2(proj2 image)));cbn [setup follow loc cpu_state cf step app option_map
   push push_words set set_regs with_zf with_words regs mem put Nat.eqb].
   rewrite SP,and_rsp_64;replace ((top-64) mod 64) with (top mod 64) by
    (replace (top-64) with (top+(-1)*64) by ring;now rewrite Z.mod_add by lia).
   pose proof(Z.mod_pos_bound top 64 ltac:(lia));change (word 3520) with 3520.
   repeat match goal with |-context[word ?x]=>rewrite (word_fits x ltac:(unfold word64;lia)) end.
   replace (o+(49+Z.of_nat 5+(stage_pc-(entry_pc+54)))) with (slide+stage_pc) by (unfold o;ring).
   rewrite (word_fits _ Dest);replace (slide+stage_pc-o) with (stage_pc-entry_pc) by (unfold o;ring);reflexivity.
 - unfold arguments;cbn [regs with_words with_zf set set_regs put Nat.eqb];repeat split;reflexivity.
Qed.

Theorem from_entry slide s c : let top:=regs s 4%nat in let o:=slide+entry_pc in
 5032<=top<2^64 -> word64(slide+stage_pc) ->
 exists u k,run 18 (ScalarBytes.fetch o symbol_bytes) (State(Running 0) s c)=
 Some(State(Running(stage_pc-entry_pc)) u k,stores o top s) /\ arguments top s u /\ regs u 5%nat=top-8 /\
 confined (fun x=>top-5032<=x<top) (stores o top s).
Proof.
 intros top o Fit Dest;destruct(FramePointer.save _ o s c top (proj1 image) eq_refl ltac:(lia)) as [f [R [SP [BP G]]]].
 destruct(push_args o top f c SP ltac:(lia)) as [a [A [Next G']]].
 destruct(first_call slide top a c Next Fit Dest) as [u [k [Call [Args FP]]]];fold o in Call.
 destruct Args as [Stack [DI [SI [DX [CX [R8 [I [BX [R12 [R13 R14]]]]]]]]]].
 exists u,k;split.
 - unfold stores;unfold spill in A|-*;rewrite (G 8%nat),(G 9%nat) in A by discriminate.
   exact (run_append _ _ _ _ _ R _ _ _ (run_append _ _ _ _ _ A _ _ _ Call)).
 - split;[unfold arguments;rewrite ?SI,?DX,?CX,?R8,?BX,?R12,?R13,?R14;repeat rewrite G' by discriminate;
           repeat rewrite G by discriminate;repeat split;assumption || reflexivity|].
   split;[now rewrite FP,G' by discriminate|]. unfold stores;apply Forall_app;split.
   + eapply Forall_impl;[|exact (FramePointer.confined o top (regs s))];intros w H x X;specialize(H x X);change (top-48<=x<top) in H;change (top-5032<=x<top);lia.
   + pose proof(Z.mod_pos_bound top 64 ltac:(lia)).
     apply Forall_forall;intros w [<-|[<-|[<-|[]]]] x X;unfold touches in X;cbn [qword call_store address size] in X;
     change (Z.of_nat 8) with 8 in X;unfold base in *;lia.
Qed.

(* The last store in this prefix is the return address pushed by CALL. *)
Lemma return_word o top s m : word64(o+54) ->
 read_word (WriteTrace.replay m (stores o top s)) (base top-8)=o+54.
Proof.
 intro W;unfold stores;rewrite !replay_app.
 apply write_read_word,W.
Qed.

Definition entered slide s c u k :=
 let top:=regs s 4%nat in let o:=slide+entry_pc in
 run 18 (MappedFetch.fetch o (length symbol_bytes)) (State(Running 0) s c)=
 Some(State(Running(stage_pc-entry_pc)) u k,stores o top s).

Record entry_state slide s u : Prop := {
 stage_arguments : arguments (regs s 4%nat) s u;
 saved_rbp : regs u 5%nat=regs s 4%nat-8;
 stage_words : well_formed u;
 stage_memory : mem u=WriteTrace.replay (mem s) (stores (slide+entry_pc) (regs s 4%nat) s);
 stage_stack_stores : confined (fun x=>regs s 4%nat-5032<=x<regs s 4%nat)
    (stores (slide+entry_pc) (regs s 4%nat) s);
 stage_return_word : read_word (mem u) (regs u 4%nat)=slide+entry_pc+54
}.

Lemma checked slide s c : let top:=regs s 4%nat in let o:=slide+entry_pc in
 well_formed s -> 5032<=top<2^64 -> word64(slide+stage_pc) -> word64(o+54) ->
 mapped (mem s) o symbol_bytes -> disjoint o (Z.of_nat(length symbol_bytes)) (top-5032) 5040 ->
 exists u k, entered slide s c u k /\ entry_state slide s u.
Proof.
 intros top o W SP T Back M Apart;destruct(from_entry slide s c SP T) as [u [k [R [Args [BP Safe]]]]].
 pose proof(run_lift _ _ _ _ _ _ _ R Safe M ltac:(unfold disjoint in Apart;intros x X Y;unfold top,o in *;lia)) as Fetch.
 pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R)) as Bytes.
 exists u,k;split;[exact Fetch|constructor];try assumption.
 - exact (mapped_run_wf _ _ _ (State (Running 0) s c) _ _ W Fetch).
 - cbn [cpu_state] in Bytes;rewrite (proj1 Args),Bytes;apply return_word,Back.
Qed.
