From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.LinkedCalls execution.WordBounds
 execution.ScalarBytes execution.InstructionRoute execution.MappedFetch execution.StoreInstructions
 memory.ByteMemory memory.WriteTrace memory.Alignment.
From Ed25519Simd.Decode Require DecoderBytes HelperBytes.
Import ListNotations. Local Open Scope Z_scope.

Definition code := DecoderBytes.symbol_bytes.
Definition origin := DecoderBytes.address.
Definition helper := HelperBytes.address.
Definition top sp := sp-40-(sp-40) mod 64-640.
Definition slot sp x := sp-40<=x<sp.
Definition saves : list line := [(0,1%nat,SaveG 5);(1,3%nat,CopyG 5 4);
 (4,1%nat,SaveG 3);(5,2%nat,SaveG 12);(7,2%nat,SaveG 13);(9,2%nat,SaveG 14)].
Definition allocate : list line := [(11,4%nat,AndImmediate 4 (-64));(15,7%nat,Sub64 4 640);
 (22,3%nat,CopyG 3 7);(25,3%nat,Copy32 12 2)].
Definition at_literal (i:nat) := helper+0xde0+8*Z.of_nat i.
Definition literal (i:nat) := let pc:=28+10*Z.of_nat i in
 (pc,10%nat,BroadcastRip (28+i) (at_literal i-(origin+pc+10))).
Definition constants := map literal (seq 0 4).
Definition invoke_setup:list line := [(68,5%nat,CallRelative (244-73))].
Lemma image : linked code saves /\ linked code allocate /\ linked code constants /\ linked code invoke_setup.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Definition args (a:cpu) (sp:Z) s :=
 regs s 4%nat=top sp /\ regs s 5%nat=sp-8 /\ regs s 7%nat=regs a 7%nat /\
 regs s 6%nat=regs a 6%nat /\ regs s 3%nat=regs a 7%nat /\ regs s 12%nat=regs a 2%nat mod 2^32.

Lemma save o s c sp : regs s 4%nat=sp -> 800<=sp<2^64 ->
 exists v ws,run 6 (ScalarBytes.fetch o code) (State (Running 0) s c)=Some(State (Running 11) v c,ws) /\
 confined (slot sp) ws /\ regs v 4%nat=sp-40 /\ regs v 5%nat=sp-8 /\
 regs v 2%nat=regs s 2%nat /\ regs v 6%nat=regs s 6%nat /\ regs v 7%nat=regs s 7%nat.
Proof.
 intros SP Fit;do 2 eexists;split;[apply (checked _ _ _ (proj1 image));reflexivity|].
 cbn [saves follow loc cf cpu_state step option_map app];unfold slot;
 cbn [snd caller_stores caller_step apply_stack stack_step result_regs result_mem target_ip with_words
   push push_words set set_regs regs mem put Nat.eqb].
 rewrite SP;repeat match goal with |- context[word ?x] =>
   rewrite (word_fits x ltac:(unfold word64 in *;lia)) end.
 split;[repeat apply Forall_cons;try apply Forall_nil;intros x X;unfold touches in X;cbn [ qword WriteTrace.address WriteTrace.size] in X;lia|].
 repeat split;lia.
Qed.

Lemma setup o s c a sp : 800<=sp<2^64 -> regs s 4%nat=sp-40 -> regs s 5%nat=sp-8 ->
 regs s 2%nat=regs a 2%nat -> regs s 6%nat=regs a 6%nat -> regs s 7%nat=regs a 7%nat ->
 exists v cf,run 4 (ScalarBytes.fetch o code) (State (Running 11) s c)=Some(State (Running 28) v cf,[]) /\
 args a sp v /\ mem v=mem s.
Proof.
 intros Fit SP BP DX SI DI;do 2 eexists;split;[apply (checked _ _ _ (proj1(proj2 image)));reflexivity|].
 cbn [allocate follow cf cpu_state loc step option_map];unfold args,top;
 cbn [with_zf regs mem set set_regs put Nat.eqb];rewrite SP,and_rsp_64;
 pose proof (Z.mod_pos_bound (sp-40) 64 ltac:(lia));
 repeat match goal with |- context[word ?x]=>rewrite (word_fits x ltac:(unfold word64 in *;lia)) end.
 repeat split;congruence || lia.
Qed.

Definition splat_value o m i := read_word m (word(o+at_literal i-origin)).
Lemma load_constants o s c :
 exists v,run 4 (ScalarBytes.fetch o code) (State (Running 28) s c)=Some(State (Running 68) v c,[]) /\
 regs v=regs s /\ mem v=mem s /\ forall i j,(i<4)%nat ->
 vectors v j (28+i)%nat=splat_value o (mem s) i.
Proof.
 eexists;split;[apply (checked _ _ _ (proj1(proj2(proj2 image))));reflexivity|].
 split;[reflexivity|split;[reflexivity|]];intros [|[|[|[|i]]]] j I;try lia;unfold splat_value;
 cbn [constants map seq literal follow loc cf cpu_state step option_map regs mem vectors put Nat.eqb];
 unfold put;cbn [Nat.eqb Nat.add];unfold at_literal;apply f_equal;apply f_equal;ring.
Qed.

Definition ready a sp s := regs s 4%nat=top sp-8 /\ regs s 5%nat=sp-8 /\
 regs s 7%nat=regs a 7%nat /\ regs s 6%nat=regs a 6%nat /\ regs s 3%nat=regs a 7%nat /\
 regs s 12%nat=regs a 2%nat mod 2^32.

Lemma inner_call o s c a sp : word64(o+244) -> 800<=sp<2^64 -> args a sp s ->
 exists v w,run 1 (ScalarBytes.fetch o code) (State (Running 68) s c)=Some(State (Running 244) v c,[w]) /\
 ready a sp v /\ read_word (mem v) (top sp-8)=word(o+73) /\
 (forall x,touches w x -> top sp-8<=x<top sp) /\ vectors v=vectors s.
Proof.
 intros Dest Fit [SP [BP [DI [SI [BX R12]]]]];do 2 eexists;split.
 - apply (checked _ _ _ (proj2(proj2(proj2 image))));cbn [invoke_setup follow step loc cpu_state cf option_map].
   replace (o+(68+Z.of_nat 5+(244-73))) with (o+244) by ring;rewrite (word_fits _ Dest).
   replace (o+244-o) with 244 by ring;reflexivity.
 - assert (Bound:word64(top sp-8)) by (unfold top,word64;pose proof(Z.mod_pos_bound (sp-40) 64 ltac:(lia));lia).
   cbn [invoke_setup follow step loc cpu_state cf option_map];unfold ready;
   cbn [push push_words with_words put Nat.eqb regs mem vectors];rewrite SP,(word_fits _ Bound).
   split;[repeat split;assumption|split].
   + apply read_word_encoded;intros k K;apply FlatMemory.write_at,K.
   + split;[intros x X;change (top sp-8<=x<top sp-8+8) in X;lia|reflexivity].
Qed.

Definition private_stack sp x := slot sp x \/ top sp-8<=x<top sp.
Theorem to_setup o s c sp : regs s 4%nat=sp -> 800<=sp<2^64 -> word64(o+244) ->
 (forall i k,(i<4)%nat -> 0<=k<8 -> ~slot sp (word(o+at_literal i-origin)+k)) ->
 exists v cf ws,run 15 (ScalarBytes.fetch o code) (State (Running 0) s c)=Some(State (Running 244) v cf,ws) /\
 ready s sp v /\ read_word (mem v) (top sp-8)=word(o+73) /\ confined (private_stack sp) ws /\
 forall i j,(i<4)%nat -> vectors v j (28+i)%nat=splat_value o (mem s) i.
Proof.
 intros SP Bounds Fit Away.
 destruct(save o s c sp SP Bounds) as [a [front [A [W [SA [BP [DX [SI DI]]]]]]]].
 destruct(setup o a c s sp Bounds SA BP DX SI DI) as [b [cf [B [Args Mem]]]].
 destruct(load_constants o b cf) as [d [D [Regs [Flat Values]]]].
 assert (Live:args s sp d) by (unfold args;rewrite Regs;exact Args).
 destruct(inner_call o d cf s sp Fit Bounds Live) as [v [w [C [Ready [Ret [Where Vec]]]]]].
 pose proof(run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ A _ _ _ B) _ _ _ D) _ _ _ C) as Whole.
 exists v,cf,(((front++[])++[])++[w]);split;[exact Whole|split;[exact Ready|split;[exact Ret|]]].
 split.
 - rewrite !app_nil_r;apply Forall_app;split.
   + eapply Forall_impl;[|exact W];intros z H x X;left;apply H,X.
   + constructor;[intros x X;right;apply Where,X|constructor].
 - intros i j I;rewrite Vec,Values,Mem by exact I;unfold splat_value.
   pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ A)) as M.
   change (mem a=WriteTrace.replay (mem s) front) in M;rewrite M.
   apply preserved_read with (outside:=fun x=>~slot sp x);
     [exact (WriteTrace.frame _ _ W (mem s))|intros k K;apply Away;assumption].
Qed.

Definition constant (i:nat) := nth i [19;2^51-1;(2^51-19)*1024;(2^51-1)*1024] 0.
Definition field_offset i := 0xde0+8*Z.of_nat i.
Lemma offsets i : (i<4)%nat -> 0<=field_offset i /\ field_offset i+8<=Z.of_nat(length HelperBytes.symbol_bytes).
Proof. intros I;unfold field_offset;change (Z.of_nat(length HelperBytes.symbol_bytes)) with 3656;lia. Qed.
Lemma literal_value i : (i<4)%nat ->
 read_word (fun x=>nth (Z.to_nat x) HelperBytes.symbol_bytes 0) (field_offset i)=constant i.
Proof. intros I;destruct i as [|[|[|[|i]]]];[vm_compute;reflexivity..|lia]. Qed.
Lemma literal_read m base bs n : mapped m base bs -> forall off,0<=off ->
 off+Z.of_nat n<=Z.of_nat(length bs) ->
 read_le n m (base+off)=read_le n (fun x=>nth (Z.to_nat x) bs 0) off.
Proof.
 intros M;induction n as [|n IH];intros off L H;[reflexivity|].
 cbn [read_le];replace (base+off+1) with (base+(off+1)) by ring;rewrite IH by lia.
 rewrite <- (M (Z.to_nat off)) by lia;now rewrite Z2Nat.id by lia.
Qed.
Lemma mapped_value m bias i : (i<4)%nat -> mapped m (bias+helper) HelperBytes.symbol_bytes ->
 WordBounds.word64 (bias+at_literal i) -> splat_value (bias+origin) m i=constant i.
Proof.
 intros I Map Fit;unfold splat_value.
 replace (bias+origin+at_literal i-origin) with (bias+at_literal i) by ring;rewrite (word_fits _ Fit).
 rewrite <- (literal_value _ I). unfold at_literal;fold (field_offset i).
 replace (bias+(helper+0xde0+8*Z.of_nat i)) with (bias+helper+field_offset i) by (unfold field_offset;ring).
 apply literal_read;[exact Map|apply offsets,I|apply offsets,I].
Qed.
