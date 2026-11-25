From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.ScalarBytes
 execution.ScalarWords execution.MappedFetch execution.InstructionRoute execution.WordBounds execution.WordSemantics
 memory.FlatMemory memory.ByteMemory memory.WriteTrace abi.SysV.
From Ed25519Simd.FullLadder Require Import LinkedBytes.
From Ed25519Simd.LadderStep Require LinkedBytes.
Import ListNotations. Local Open Scope Z_scope.
Module L:=Ed25519Simd.LadderStep.LinkedBytes.

Inductive site:=Four | Affine | Even.
Definition start k:Z:=match k with Four=>768 | Affine=>776 | Even=>802 end.
Definition next k:Z:=match k with Four=>776 | Affine=>802 | Even=>822 end.
Definition target k:=match k with Four=>L.double4_pc | _=>L.cached_pc end.
Definition displacement k:=target k-(entry_pc+next k).
Definition code k:list line:=let off:=start k in
 [(off,3%nat,CopyG 7 3)]++
 (match k with Four=>[] | Affine=>[(off+3,8%nat,LeaG 6 (Address 4 None 1280));
    (off+11,5%nat,Imm32 2 1);(off+16,5%nat,Imm32 1 1)]
 | Even=>[(off+3,8%nat,LeaG 6 (Address 4 None 2240));(off+11,2%nat,Zero32 2);(off+13,2%nat,Zero32 1)] end)++
 [(next k-5,5%nat,CallRelative(displacement k))].
Lemma image k:linked symbol_bytes (code k).
Proof. destruct k;repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Definition enter slide k:=segment (slide+entry_pc) symbol_bytes (length(code k)).
Definition push_store slide k base:=qword (word(slide+entry_pc+(next k-5))) (base-8) (slide+entry_pc+next k).
Definition flags k c:=match k with Even=>Some false|_=>c end.
Definition args k pt base s:=regs s 4%nat=base-8 /\ regs s 7%nat=pt /\ match k with Four=>True
 | Affine=>regs s 6%nat=base+1280 /\ regs s 2%nat=1 /\ regs s 1%nat=1
 | Even=>regs s 6%nat=base+2240 /\ regs s 2%nat=0 /\ regs s 1%nat=0 end.

Lemma transfer slide k pt base s c : regs s 4%nat=base -> regs s 3%nat=pt ->
 8<=base -> base+3520<=2^64 -> word64(slide+target k) ->
 exists u,run (length(code k)) (ScalarBytes.fetch (slide+entry_pc) symbol_bytes)
   (State(Running(start k)) s c)=Some(State(Running(target k-entry_pc)) u (flags k c),[push_store slide k base]) /\
 args k pt base u /\ (forall r,In r sysv_saved -> regs u r=regs s r).
Proof.
 intros SP BX Low High Dest;destruct k;eexists;split.
 1,3,5:apply (InstructionRoute.checked _ _ _ (image _));
   cbn [code start next flags follow step cpu_state cf loc option_map push push_words regs set set_regs
        with_zf with_words Instructions.put Nat.eqb effective app];
   rewrite SP,BX,?Z.add_0_r;
   try rewrite (word_fits (base+1280)) by (unfold word64;lia);try rewrite (word_fits (base+2240)) by (unfold word64;lia);
   rewrite (word_fits (base-8)) by (unfold word64;lia);
   match goal with |-context[word (?o+(?a+Z.of_nat ?n+displacement ?k))]=>
     replace (o+(a+Z.of_nat n+displacement k)) with (slide+target k) by (unfold displacement,next;ring) end;
   rewrite (word_fits _ Dest);
   match type of Dest with word64 (_+?t)=>replace (slide+t-(slide+entry_pc)) with (t-entry_pc) by ring end;reflexivity.
 all:split;[unfold args;repeat split;reflexivity|intros r [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];reflexivity].
Qed.

Record entry slide k pt base p q:Prop:=Entry {
 at_child:ip q=slide+target k;
 ready:well_formed(machine q);
 arguments:args k pt base (machine q);
 saved:forall r,In r sysv_saved -> regs(machine q) r=regs(machine p) r;
 pushed:mem(machine q)=store_word (mem(machine p)) (base-8) (slide+entry_pc+next k);
 return_word:read_word (mem(machine q)) (base-8)=slide+entry_pc+next k;
 stores:log q=log p++[push_store slide k base]
}.

Theorem checked slide k pt base p : ip p=slide+entry_pc+start k -> well_formed(machine p) ->
 regs(machine p) 4%nat=base -> regs(machine p) 3%nat=pt -> 8<=base -> base+3520<=2^64 ->
 word64(slide+target k) -> word64(slide+entry_pc+next k) ->
 mapped (mem(machine p)) (slide+entry_pc) symbol_bytes ->
 disjoint (slide+entry_pc) (Z.of_nat(length symbol_bytes)) (base-8) 8 ->
 exists q,enter slide k p=Some q /\ entry slide k pt base p q.
Proof.
 intros PC W SP BX Low High D Back Map Apart.
 destruct(transfer _ _ _ _ _ (carry p) SP BX Low High D) as [u [R [Args G]]].
 assert (Safe:confined (fun x=>base-8<=x<base) [push_store slide k base]).
 { constructor;[intros x X;change (base-8<=x<base-8+8) in X;lia|constructor]. }
 pose proof(run_lift _ _ _ _ _ _ _ R Safe Map ltac:(unfold disjoint in Apart;intros x X Y;lia)) as Run.
 set(q:=Cursor (slide+target k) u (flags k (carry p)) (log p++[push_store slide k base])).
 assert (End:enter slide k p=Some q).
 { unfold enter,segment;rewrite PC;replace (slide+entry_pc+start k-(slide+entry_pc)) with (start k) by ring.
   rewrite Run;unfold q;cbn [option_map finish absolute loc cpu_state cf];f_equal;f_equal;ring. }
 assert (M:mem u=store_word (mem(machine p)) (base-8) (slide+entry_pc+next k))
   by exact (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R)).
 exists q;split;[exact End|constructor];try assumption;try reflexivity.
 - exact (segment_wf _ _ _ _ _ W End).
 - change (read_word (mem u) (base-8)=slide+entry_pc+next k);rewrite M;apply write_read_word,Back.
Qed.
