From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute execution.StoreHistory
 memory.MemoryGeometry memory.FlatMemory memory.ByteMemory memory.WriteTrace abi.SysV.
From Ed25519Simd.FullLadder Require Import LinkedBytes Program Native Audit LoopFrame.
From Ed25519Simd.FullLadder Require LoopStage LoopStageCall LoopSlots.
Import ListNotations. Local Open Scope Z_scope.
Definition path (last:bool):list line:=[(853,3%nat,CopyG 7 3);(856,3%nat,CopyG 6 4);(859,2%nat,Zero32 2);
 (861,4%nat,Compare32 15 1);(865,2%nat,Branch Unequal 3)]++
 (if last then [(867,3%nat,Load32 2 (Address 5 None (-56)))] else [])++
 [(870,5%nat,CallRelative (L.wrapper_pc-(entry_pc+875)))].
Lemma image last:linked symbol_bytes (path last).
Proof. destruct last;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition last s:=(regs s 15%nat mod 2^32=?1).
Definition enter slide p:=segment (slide+entry_pc) symbol_bytes (length(path(last(machine p)))) p.
Definition push_store slide s:=qword (word(slide+entry_pc+870)) (base_of s-8) (slide+entry_pc+875).
Definition args s full v:=regs v 4%nat=base_of s-8 /\ regs v 7%nat=regs s 7%nat /\ regs v 6%nat=base_of s /\ regs v 2%nat=bits full.

Lemma transfer slide s full v n c:placement slide s -> well_formed s -> intact slide s v -> regs s 9%nat=bits full ->
 regs v 4%nat=base_of s -> regs v 15%nat=Z.of_nat n+1 -> (n<31)%nat ->
 exists u, MappedFetch.run (length(path(last v))) (ScalarBytes.fetch (slide+entry_pc) symbol_bytes)
 (ScalarBytes.State(Running 853) v c)=Some(ScalarBytes.State(Running(L.wrapper_pc-entry_pc)) u (Some false),[push_store slide s]) /\
 args s (full && Nat.eqb n 0) u /\ forall g,In g sysv_saved -> regs u g=regs v g.
Proof.
 intros P W F Mode SP C N;pose proof(frame_pointer _ _ _ F) as BP;pose proof(accumulator _ _ _ F) as PT.
 pose proof(frame_range _ _ P) as Range;pose proof(Z.mod_pos_bound (top s) 64 ltac:(lia)) as Pad.
 destruct(loaded_images _ _ P _ _ (or_intror(or_intror(or_introl eq_refl)))) as [Dest _].
 assert (Size:0<LA.wrapper_size) by (vm_compute;reflexivity).
 assert (Fit:word64(slide+L.wrapper_pc)) by (unfold fits64,word64 in *;lia).
 assert (Stack:word(base_of s-8)=base_of s-8) by (apply word_fits;unfold top,base_of,staging,pad_of,word64,fits64 in *;lia).
 assert (Slot:word(top s-8+0+ -56)=top s-64) by (replace (top s-8+0+ -56) with (top s-64) by ring;apply word_fits;unfold top,word64,fits64 in *;lia).
 pose proof(proj2(LoopSlots.arguments _ _ _ F W)) as Arg;rewrite Mode in Arg.
 assert (Flag:bits full mod 2^32=bits full) by (destruct full;reflexivity);rewrite Flag in Arg.
 set(t:=Z.of_nat n+1) in *;assert (Low:t mod 2^32=t) by (apply Z.mod_small;unfold t;lia).
 assert (Carry:(t<?1)=false) by (apply Z.ltb_ge;unfold t;lia).
 assert (Last:(t=?1)=Nat.eqb n 0) by (destruct n;[reflexivity|apply Z.eqb_neq;unfold t;lia]).
 assert (Which:last v=Nat.eqb n 0) by (unfold last;now rewrite C,Low).
 rewrite Which;destruct(Nat.eqb n 0) eqn:Zero;eexists;split.
 1,3:apply (InstructionRoute.checked _ _ _ (image _));cbn [path follow ScalarBytes.step loc cpu_state cf option_map app
    eval_condition with_zf effective push push_words LinkedCalls.set set_regs with_words regs mem flag Instructions.put Nat.eqb];
    rewrite C,Low;change (1 mod 2^32) with 1;rewrite Last,Carry;
    cbn [negb option_map follow loc cpu_state cf flag with_zf];cbn [ScalarBytes.step with_zf effective push push_words LinkedCalls.set set_regs with_words regs mem Instructions.put Nat.eqb option_map app];
    rewrite ?PT,?BP,?Slot,?Arg,SP,Stack;
    replace (slide+entry_pc+(870+Z.of_nat 5+(L.wrapper_pc-(entry_pc+875)))) with (slide+L.wrapper_pc) by ring;
    rewrite (word_fits _ Fit);replace (slide+L.wrapper_pc-(slide+entry_pc)) with (L.wrapper_pc-entry_pc) by ring;reflexivity.
 all:split;[unfold args;rewrite ?Bool.andb_true_r,?Bool.andb_false_r;repeat split;reflexivity|
  intros g [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];reflexivity].
Qed.

Record entry slide s full n p q:Prop:=Entry {
 address:ip q=slide+L.wrapper_pc; words:well_formed(machine q); parameters:args s (full && Nat.eqb n 0) (machine q);
 saved:forall g,In g sysv_saved -> regs(machine q) g=regs(machine p) g;
 link:read_word (mem(machine q)) (base_of s-8)=slide+entry_pc+875;
 writes:StoreHistory.extends (LoopStageCall.slot s) p q
}.
Theorem checked slide s full n p : placement slide s -> well_formed s -> well_formed(machine p) -> intact slide s (machine p) ->
 regs s 9%nat=bits full -> ip p=slide+entry_pc+853 -> regs(machine p) 4%nat=base_of s ->
 regs(machine p) 15%nat=Z.of_nat n+1 -> (n<31)%nat -> mapped (mem(machine p)) (slide+entry_pc) symbol_bytes ->
 exists q,enter slide p=Some q /\ entry slide s full n p q.
Proof.
 intros P W WF F Mode PC SP Count N Map;destruct(transfer _ _ _ _ _ (carry p) P W F Mode SP Count N) as [u [R [Args G]]].
 assert (Safe:confined (LoopStageCall.slot s) [push_store slide s]).
 { constructor;[intros x X;change (base_of s-8<=x<base_of s-8+8) in X;unfold LoopStageCall.slot;lia|constructor]. }
 destruct(loaded_images _ _ P _ _ (or_introl eq_refl)) as [Fits _].
 pose proof(LoopStage.outside_image _ _ _ _ P (or_introl eq_refl)) as Sep.
 destruct(StoreHistory.segment_checked _ _ _ _ _ _ _ _ PC Map
   ltac:(intros x X H;apply (Sep x X),(LoopStageCall.slot_work _ _ H)) R Safe) as [Run Hist].
 eexists;split;[exact Run|constructor];try exact Args;try exact G;try exact Hist.
 - cbn [finish ip absolute loc];ring.
 - exact (segment_wf _ _ _ _ _ WF Run).
 - cbn [finish machine cpu_state];pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R)) as M;cbn [cpu_state] in M;rewrite M.
   apply write_read_word;assert (875<Z.of_nat(length symbol_bytes)) by (vm_compute;reflexivity);unfold fits64,word64 in *;lia.
Qed.
