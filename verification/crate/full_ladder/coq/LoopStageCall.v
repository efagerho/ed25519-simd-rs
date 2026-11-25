From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.ScalarBytes
 execution.ScalarWords execution.MappedFetch execution.InstructionRoute execution.WordBounds execution.WordSemantics
 execution.StoreHistory memory.MemoryGeometry memory.FlatMemory memory.ByteMemory memory.WriteTrace abi.SysV.
From Ed25519Simd.FullLadder Require Import LinkedBytes Program Operands Audit FirstStage LoopFrame.
From Ed25519Simd.FullLadder Require LoopSlots.
Import ListNotations. Local Open Scope Z_scope.

Definition path:list line:=[(828,3%nat,CopyG 7 4);(831,3%nat,CopyG 6 12);(834,3%nat,CopyG 2 13);
 (837,3%nat,CopyG 1 14);(840,4%nat,Load64 8 (Address 5 None (-48)));(844,4%nat,LeaG 9 (Address 15 None (-1)));
 (848,5%nat,CallRelative (stage_pc-(entry_pc+853)))].
Lemma linked_path:linked symbol_bytes path.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition enter slide:=segment (slide+entry_pc) symbol_bytes 7.
Definition push_store slide s:=qword (word(slide+entry_pc+848)) (base_of s-8) (slide+entry_pc+853).
Definition slot s x:=base_of s-8<=x<base_of s.
Definition staged_args s n v:=regs v 4%nat=base_of s-8 /\ regs v 7%nat=base_of s /\
 regs v 6%nat=regs s 6%nat /\ regs v 2%nat=regs s 2%nat /\ regs v 1%nat=regs s 1%nat /\
 regs v 8%nat=regs s 8%nat /\ regs v 9%nat=Z.of_nat n.
Lemma args_for s n v : staged_args s n v -> stage_registers s (pad_of s) n v.
Proof. intros [SP [DI [SI [DX [CX [R8 Idx]]]]]] r [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];assumption. Qed.

Lemma transfer slide s p c (n:nat) : placement slide s -> intact slide s p -> well_formed s ->
 regs p 4%nat=base_of s -> regs p 15%nat=Z.of_nat n+1 -> (n<31)%nat ->
 exists u,MappedFetch.run 7 (ScalarBytes.fetch (slide+entry_pc) symbol_bytes) (ScalarBytes.State(Running 828) p c)=
 Some(ScalarBytes.State(Running(stage_pc-entry_pc)) u c,[push_store slide s]) /\ staged_args s n u /\
 forall g,In g sysv_saved -> regs u g=regs p g.
Proof.
 intros P F W SP Count N;destruct(LoopSlots.arguments _ _ _ F W) as [Digit Mode].
 pose proof(frame_pointer _ _ _ F) as BP;pose proof(frame_range _ _ P) as Range.
 destruct(loaded_images _ _ P _ _ (or_intror(or_introl eq_refl))) as [Target _].
 assert (Sz:0<Z.of_nat(length StageRound.ObjectBytes.symbol_bytes)) by (vm_compute;reflexivity).
 assert (Fits:word64(slide+stage_pc)) by (unfold fits64,word64 in *;lia).
 pose proof(Z.mod_pos_bound (top s) 64 ltac:(lia)) as Pad.
 assert (Stack:word(base_of s-8)=base_of s-8) by
    (apply word_fits;unfold base_of,staging,pad_of,top,fits64,word64 in *;lia).
 assert (Src:word(top s-8+0+ -48)=top s-56) by
    (replace (top s-8+0+ -48) with (top s-56) by ring;apply word_fits;unfold top,fits64,word64 in *;lia).
 assert (Pair:word(Z.of_nat n+1+0+ -1)=Z.of_nat n) by
   (replace (Z.of_nat n+1+0+ -1) with (Z.of_nat n) by ring;apply word_fits;unfold word64;lia).
 eexists;split.
 - apply (InstructionRoute.checked _ _ _ linked_path);cbn [path follow ScalarBytes.step loc cpu_state cf option_map app effective push push_words regs mem with_words LinkedCalls.set set_regs put Nat.eqb].
   rewrite BP,Count,Src,Pair,Digit,SP,Stack,(keys _ _ _ F),(base_table _ _ _ F),(scalar _ _ _ F).
   replace (slide+entry_pc+(848+Z.of_nat 5+(stage_pc-(entry_pc+853)))) with (slide+stage_pc) by ring.
   rewrite (word_fits _ Fits);replace (slide+stage_pc-(slide+entry_pc)) with (stage_pc-entry_pc) by ring;reflexivity.
 - split;[unfold staged_args;repeat split;reflexivity|intros g [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];reflexivity].
Qed.

Record entry slide s n p q:Prop:=Entry {
 at_stage:ip q=slide+stage_pc; words:well_formed(machine q);
 args:staged_args s n (machine q); frame:intact slide s (machine q);
 saved:forall r,In r sysv_saved -> regs(machine q) r=regs(machine p) r;
 back:read_word (mem(machine q)) (base_of s-8)=slide+entry_pc+853;
 writes:StoreHistory.extends (slot s) p q
}.
Lemma slot_work s x:slot s x -> writable s x.
Proof. intro X;right;unfold slot,base_of,pad_of,staging,top in *;pose proof(Z.mod_pos_bound (regs s 4%nat) 64 ltac:(lia));lia. Qed.
Theorem checked slide s p n : placement slide s -> well_formed s -> well_formed(machine p) -> intact slide s (machine p) ->
 ip p=slide+entry_pc+828 -> regs(machine p) 4%nat=base_of s -> regs(machine p) 15%nat=Z.of_nat n+1 -> (n<31)%nat ->
 mapped (mem(machine p)) (slide+entry_pc) symbol_bytes ->
 exists q,enter slide p=Some q /\ entry slide s n p q.
Proof.
 intros P W WF F PC SP Count N Map;destruct(transfer _ _ _ (carry p) _ P F W SP Count N) as [u [R [Args G]]].
 assert (Safe:confined (slot s) [push_store slide s]).
 { constructor;[intros x X;change (base_of s-8<=x<base_of s-8+8) in X;unfold slot;lia|constructor]. }
 destruct(loaded_images _ _ P _ _ (or_introl eq_refl)) as [Text [_ Sep]].
 assert (Code:forall x,slide+entry_pc<=x<slide+entry_pc+Z.of_nat(length symbol_bytes) -> ~slot s x).
 { intros x X Y;destruct(slot_work s x Y) as [Point|Stack];unfold slot,base_of,pad_of,staging,top,disjoint in *;
   pose proof(Z.mod_pos_bound (regs s 4%nat) 64 ltac:(lia));lia. }
 pose proof(run_lift _ _ _ _ _ _ _ R Safe Map Code) as Run.
 set(q:=Cursor (slide+stage_pc) u (carry p) (log p++[push_store slide s])).
 assert (End:enter slide p=Some q).
 { unfold enter,segment;rewrite PC;replace (slide+entry_pc+828-(slide+entry_pc)) with 828 by ring.
   rewrite Run;unfold q;cbn [option_map finish absolute loc cpu_state cf];f_equal;f_equal;ring. }
 assert (Hist:StoreHistory.extends (slot s) p q) by
  (exists [push_store slide s];split;[reflexivity|split;[exact Safe|intro x;exact (f_equal (fun m=>m x) (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R)))]]).
 exists q;split;[exact End|constructor];try assumption;try reflexivity.
 - exact (segment_wf _ _ _ _ _ WF End).
 - eapply after;[exact P|exact F|intros g K;apply G;unfold live,sysv_saved in *;simpl in *;tauto|
    exact (StoreHistory.lend _ _ _ _ (slot_work s) Hist)].
 - change (read_word (mem u) (base_of s-8)=slide+entry_pc+853);pose proof (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R)) as M.
   cbn [cpu_state] in M;rewrite M.
   apply write_read_word;assert (853<Z.of_nat(length symbol_bytes)) by (vm_compute;reflexivity);unfold fits64,word64 in *;lia.
Qed.
