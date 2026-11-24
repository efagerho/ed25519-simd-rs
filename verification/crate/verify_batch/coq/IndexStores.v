From Coq Require Import List ZArith Lia Bool.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.MappedFetch execution.FrameInstructions memory.MemoryGeometry
 memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Image Rows Return EntryWrites Prologue DescriptorStores StageWrites.
Import ListNotations. Local Open Scope Z_scope.

Definition pair j : list line :=
 let src:=40*Z.of_nat j+32 in
 [(if src<?128 then 4%nat else 7%nat,Load64 0 (Address 3 None src));
  (8%nat,Store64 0 (Address 4 None (864+8*Z.of_nat j)))].
Definition index_slot frame j := frame+864+8*Z.of_nat j.
Definition source_slot base j := base+40*Z.of_nat j+32.
Definition args frame base s := regs s 4%nat=frame /\ regs s 3%nat=base.
Definition metadata frame count idx m := read_word m (frame+928)=count /\
 forall j,(j<8)%nat -> read_word m (index_slot frame j)=idx j.

Lemma one o text off frame base j s c : 0<=off -> (j<8)%nat ->
 decoded text off (pair j) -> fits64 base 320 -> fits64 frame 960 -> args frame base s ->
 exists t ws,run 2 (ScalarBytes.fetch o text) (State (Running off) s c)=
 Some(State (Running (off+FrameInstructions.width (pair j))) t c,ws) /\ args frame base t /\
 mem t=store_word (mem s) (index_slot frame j) (read_word (mem s) (source_slot base j)).
Proof.
 intros O J [Load [Store _]] [B BU] [F FU] [SP BX].
 unfold pair in Load,Store|-*;set (n:=if 40*Z.of_nat j+32<?128 then 4%nat else 7%nat) in *.
 cbn [run];rewrite (fetch_at o text off s c n _ O Load);cbn [step].
 rewrite (fetch_at o text (off+Z.of_nat n) _ _ _ _ ltac:(lia) Store);cbn [step option_map app].
 do 2 eexists;split.
 - unfold FrameInstructions.width;cbn [fold_right fst];replace (off+(Z.of_nat n+(Z.of_nat 8+0))) with (off+Z.of_nat n+Z.of_nat 8) by ring;reflexivity.
 - split;[exact (conj SP BX)|]. cbn [mem with_words set set_regs regs effective put Nat.eqb].
   rewrite SP,BX,!Z.add_0_r. repeat rewrite word_fits by (unfold word64;lia).
   unfold index_slot,source_slot;replace (base+(40*Z.of_nat j+32)) with (base+40*Z.of_nat j+32) by ring.
   replace (frame+(864+8*Z.of_nat j)) with (frame+864+8*Z.of_nat j) by ring;rewrite (word_fits (frame+864+8*Z.of_nat j)),(word_fits (base+40*Z.of_nat j+32)) by (unfold word64;lia);reflexivity.
Qed.

Lemma copied o text frame base idx active :
 fits64 base 320 -> fits64 frame 960 -> disjoint base 320 (frame+864) 64 ->
 (forall j,(j<8)%nat -> word64(idx j)) ->
 forall n j off s c,(j+n=8)%nat -> 0<=off -> decoded text off (flat_map pair (seq j n)) ->
 args frame base s -> (forall i,(i<8)%nat -> read_word (mem s) (source_slot base i)=idx i) ->
 read_word (mem s) (frame+928)=active ->
 (forall i,(i<j)%nat -> read_word (mem s) (index_slot frame i)=idx i) ->
 exists t ws,run (2*n) (ScalarBytes.fetch o text) (State (Running off) s c)=
 Some(State (Running (off+FrameInstructions.width (flat_map pair (seq j n)))) t c,ws) /\ args frame base t /\ metadata frame active idx (mem t).
Proof.
 intros Base Frame Sep Words n;induction n as [|n IH];intros j off s c Count O Code G Source Active Old.
 - replace j with 8%nat in * by lia. cbn [seq flat_map FrameInstructions.width fold_right];rewrite Z.add_0_r.
   do 2 eexists;split;[reflexivity|exact (conj G (conj Active Old))].
 - cbn [seq flat_map] in Code|-*. destruct (prefix_decoded _ _ _ _ Code) as [Pair Tail].
   destruct(one o text off frame base j s c O ltac:(lia) Pair Base Frame G) as [u [own [R [U M]]]].
   rewrite Source in M by lia.
   assert (Offset:0<=FrameInstructions.width (pair j)) by
     (unfold FrameInstructions.width,pair;cbn [fold_right fst];destruct (_<?_);lia).
   destruct(IH (S j) (off+FrameInstructions.width(pair j)) u c ltac:(lia) ltac:(lia) Tail U) as [last [tail [Rest End]]].
   + intros i I;rewrite M,read_other_word by (unfold index_slot,source_slot,disjoint in *;lia);apply Source,I.
   + rewrite M,read_other_word by (unfold index_slot,disjoint;lia);exact Active.
   + intros i I;rewrite M;destruct (Nat.eq_dec i j) as [->|NE].
     * apply read_word_exact;[apply Words;lia|intros k K;unfold store_word;apply write_at,K].
     * rewrite read_other_word by (unfold index_slot,disjoint;lia);apply Old;lia.
   + exists last,(own++tail);split;[|exact End].
     replace (2*S n)%nat with (2+2*n)%nat by lia.
     assert (Width:forall a b, FrameInstructions.width (a++b)=FrameInstructions.width a+FrameInstructions.width b).
     { intros a b;induction a;unfold FrameInstructions.width in *;cbn;[ring|now rewrite IHa,Z.add_assoc]. }
     rewrite Width,Z.add_assoc;exact (run_append _ _ _ _ _ R _ _ _ Rest).
Qed.

Definition allowed_inputs frame base := disjoint base 320 (frame+512) 424.
Theorem transfer o text delta e s c child ws base idx active :
 StageWrites.bound text delta -> placement e -> args (Rows.frame e) base s ->
 fits64 base 320 -> allowed_inputs (Rows.frame e) base ->
 (forall j,(j<8)%nat -> word64(idx j) /\ read_word (mem s) (source_slot base j)=idx j) ->
 read_word (mem s) (Rows.frame e+928)=active ->
 run 42 (ScalarBytes.fetch o text) (State (Running (offset Stage)) s c)=Some(child,ws) ->
 metadata (Rows.frame e) active idx (mem(cpu_state child)).
Proof.
 intros [Code Invoke] P [SP BX] Base Sep Rows Count Run.
 set (frame:=Rows.frame e) in *.
 assert (Fit:fits64 frame 960) by (destruct(stack_ok _ P) as [[A B] _];unfold frame,Rows.frame,sp,fits64 in *;lia).
 destruct (prefix_decoded _ _ inputs _ Code) as [Loads Rest].
 set (after_load:=offset Stage+FrameInstructions.width inputs) in *.
 destruct (prefix_decoded _ after_load publish _ Rest) as [Stores Rest'].
 set (after_store:=after_load+FrameInstructions.width publish) in *.
 destruct (prefix_decoded _ after_store StageWrites.indices _ Rest') as [Pairs Finish].
 pose proof (DescriptorStores.read_block o text Routing.transpose (offset Stage) s c ltac:(change (0<=82);lia) Loads) as L.
 set (loaded:=load_vectors Routing.transpose s) in *.
 destruct (store_block o text frame (seq 0 4) Fit ltac:(repeat constructor;lia)
   after_load loaded c ltac:(change (0<=166);lia) Stores SP) as [writes V].
 set (st:=stored frame (seq 0 4) loaded) in *.
 assert (Outside:forall x,~(frame+512<=x<frame+768) -> mem st x=mem s x).
 { intros x X;unfold st;cbn [stored seq fold_left store_vector mem with_words].
   unfold bank;repeat rewrite write_outside by (cbn;lia);reflexivity. }
 destruct (copied o text frame base idx active Base Fit ltac:(unfold allowed_inputs,disjoint in *;lia)
    ltac:(intros i I;exact (proj1(Rows i I))) 8 0 after_store st c eq_refl ltac:(change (0<=197);lia) Pairs (conj SP BX))
     as [mid [indices [Copy [[Top _] M]]]].
 - intros i I;rewrite <- (proj2(Rows i I));apply preserved_read with (outside:=fun x=>~(frame+512<=x<frame+768)).
   + exact Outside.
   + intros k K;change (0<=k<8) in K;unfold source_slot,allowed_inputs,disjoint in *;lia.
 - rewrite <-Count;apply preserved_read with (outside:=fun x=>~(frame+512<=x<frame+768));[exact Outside|intros k K;lia].
 - intros i I;lia.
 - set (lastops:=[(7%nat,Add64 3 320)]++setup).
   set (off:=after_store+FrameInstructions.width StageWrites.indices) in *.
   destruct (sequence o text 0 0 frame lastops ltac:(lia) ltac:(unfold fits64 in *;lia)
      eq_refl off mid c ltac:(vm_compute;discriminate) Finish Top) as [args [ca [zs [F [Stack Empty]]]]].
   change (off+FrameInstructions.width lastops) with (offset CallPrepare) in F.
   assert (Same:forall x,mem args x=mem mid x).
   { intro x;pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ F)) as E;cbn [cpu_state] in E.
     rewrite E;apply (WriteTrace.frame _ _ Empty);lia. }
   assert (Last:exists final tail,run 1 (ScalarBytes.fetch o text) (State (Running (offset CallPrepare)) args ca)=
        Some(final,tail) /\ mem(cpu_state final)=store_word (mem args) (frame-8) (o+offset Prepared)).
   { cbn [run];rewrite (fetch_at o text (offset CallPrepare) args ca 5 _ ltac:(change (0<=380);lia) Invoke).
     cbn [step option_map app];do 2 eexists;split;[reflexivity|].
     change (store_word (mem args) (word(regs args 4%nat-8)) (o+offset Prepared)=store_word (mem args) (frame-8) (o+offset Prepared)).
     rewrite Stack,word_fits by (destruct(stack_ok _ P) as [[A B] _];unfold frame,Rows.frame,sp,word64 in *;lia);reflexivity. }
   destruct Last as [v [events [Call Mem]]].
   pose proof (run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ L _ _ _ V)
      _ _ _ Copy) _ _ _ F) _ _ _ Call) as Total.
   change (run 42 (ScalarBytes.fetch o text) (State (Running (offset Stage)) s c)=Some(v,((([]++writes)++indices)++zs)++events)) in Total.
   rewrite Run in Total;injection Total as <- _.
   destruct M as [AC IDX];split;[rewrite <- AC|intros i I;rewrite <- (IDX i I)];rewrite Mem.
   all: apply preserved_read with (outside:=fun x=>frame<=x);
      [intros x X;unfold store_word;rewrite write_outside by lia;apply Same|intros k K;unfold index_slot;lia].
Qed.

Lemma metadata_preserved frame active idx m m' :
 (forall x,frame+864<=x<frame+936 -> m' x=m x) -> metadata frame active idx m ->
 metadata frame active idx m'.
Proof.
 intros Same [A I];split;[rewrite <-A|intros j J;rewrite <- (I j J)].
 all: apply preserved_read with (outside:=fun x=>frame+864<=x<frame+936);
  [exact Same|intros k K;change (0<=k<8) in K;unfold index_slot;lia].
Qed.
