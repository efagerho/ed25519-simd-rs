From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls
 execution.ScalarBytes execution.MappedFetch execution.InstructionRoute
 memory.FlatMemory memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Machine Require execution.PreservedRegister.
From Ed25519Simd.PrepareChunk Require CommonBytes.
From Ed25519Simd.Decode Require DecoderBytes.
Import ListNotations. Local Open Scope Z_scope.

Definition common := CommonBytes.address.
Definition decoder := DecoderBytes.address.
Definition start : list line :=
 [(65,2%nat,Test32 0);(67,6%nat,Branch Equal (260-73));(73,3%nat,Copy32 14 0);(76,2%nat,Zero32 1)].
Definition copies : list line :=
 [(78,3%nat,Load64 7 (Address 15 None 0));(81,4%nat,Load64 6 (Address 15 None 64));
  (85,4%nat,LoadY 0 (Address 7 None 0));(89,4%nat,LoadY 1 (Address 6 None 0));
  (93,5%nat,StoreAlignedY 0 (Address 3 (Some (1%nat,1)) 0));
  (98,9%nat,StoreAlignedY 1 (Address 3 (Some (1%nat,1)) 256))].
Definition increment : list line :=
 [(107,4%nat,Add64 15 8);(111,3%nat,Add32 1 32);(114,6%nat,Compare32 1 256);
  (120,2%nat,Branch Unequal (78-122))].
Definition call : list line :=
 [(122,7%nat,LeaG 7 (Address 3 None 1024));(129,3%nat,LeaG 6 (Address 3 None 0));
  (132,5%nat,Imm32 2 2);(137,5%nat,CallRelative (decoder-(common+142)))].

Lemma code : linked CommonBytes.symbol_bytes start /\ linked CommonBytes.symbol_bytes copies /\
 linked CommonBytes.symbol_bytes increment /\ linked CommonBytes.symbol_bytes call.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Definition run_common slide := ScalarBytes.fetch (slide+common) CommonBytes.symbol_bytes.
Definition holds frame dst table mask j s :=
 regs s 4%nat=frame /\ regs s 3%nat=dst /\ regs s 14%nat=mask /\
 regs s 15%nat=table+8*Z.of_nat j /\ regs s 1%nat=32*Z.of_nat j.
Lemma started slide s c frame dst table : regs s 0%nat mod 2^32<>0 ->
 regs s 4%nat=frame -> regs s 3%nat=dst -> regs s 15%nat=table ->
 exists u,run 4 (run_common slide) (State (Running 65) s c)=Some(State (Running 78) u (Some false),[]) /\
 holds frame dst table (regs s 0%nat mod 2^32) 0 u /\ mem u=mem s.
Proof.
 intros Nonzero SP BX R15. apply Z.eqb_neq in Nonzero.
 eexists;split;[apply (checked _ _ _ (proj1 code));cbn [start follow loc cf cpu_state step
  eval_condition with_zf flag option_map];rewrite Nonzero;reflexivity|].
 unfold holds;cbn [start follow loc cf cpu_state step eval_condition with_zf flag option_map set set_regs
 regs mem put Nat.eqb];try rewrite Nonzero;cbn [loc cf cpu_state step eval_condition with_zf flag option_map
 set set_regs regs mem put Nat.eqb];cbn [Z.of_nat];rewrite Z.mul_0_r,Z.add_0_r;repeat split;auto.
Qed.

Definition ymm m a j := if (j<?4)%nat then read_word m (a+8*Z.of_nat j) else 0.
Definition pair_memory m a b d :=
 write_bytes (write_bytes m d 32 (vector_byte (ymm m a))) (d+256) 32 (vector_byte (ymm m b)).
Lemma copied_bytes m a k : byte_memory m -> 0<=k<32 -> vector_byte (ymm m a) k=m(a+k).
Proof.
 intros B K;unfold vector_byte,ymm.
 assert (L:0<=k/8<4) by (split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia).
 rewrite (proj2 (Nat.ltb_lt (Z.to_nat(k/8)) 4) ltac:(lia)),Z2Nat.id by lia.
 rewrite read_word_byte by (auto;apply Z.mod_pos_bound;lia).
 f_equal;pose proof (Z.div_mod k 8 ltac:(lia));lia.
Qed.

Lemma pair_at m a b d (second:bool) k : byte_memory m -> 0<=k<32 ->
 pair_memory m a b d (d+(if second then 256 else 0)+k)=m((if second then b else a)+k).
Proof.
 intros B K;unfold pair_memory;destruct second;[rewrite write_at by lia|rewrite Z.add_0_r,write_outside,write_at by lia];
 apply copied_bytes;assumption.
Qed.
Lemma pair_out m a b d x : ~(d<=x<d+32) -> ~(d+256<=x<d+288) -> pair_memory m a b d x=m x.
Proof. unfold pair_memory;intros;rewrite !write_outside by lia;reflexivity. Qed.

Lemma copy_pair slide frame dst table mask j s c a b :
 holds frame dst table mask j s -> (j<8)%nat -> dst mod 32=0 ->
 fits64 dst 512 -> fits64 table 128 -> word64 a -> word64 b ->
 read_word (mem s) (table+8*Z.of_nat j)=a -> read_word (mem s) (table+64+8*Z.of_nat j)=b ->
 exists u w,run 6 (run_common slide) (State (Running 78) s c)=Some(State (Running 107) u c,w) /\
 holds frame dst table mask j u /\
 mem u=pair_memory (mem s) a b (dst+32*Z.of_nat j) /\
 confined (fun x=>dst<=x<dst+512) w.
Proof.
 intros H J Align [D U] [T V] A B First Second. destruct H as [SP [BX [Mask [Row Off]]]].
 set (d:=dst+32*Z.of_nat j). assert (Al:d mod 32=0).
 { unfold d;rewrite Z.mul_comm,Z.mod_add by lia;exact Align. }
 assert (Ah:(d+256) mod 32=0) by (replace 256 with (8*32) by reflexivity;rewrite Z.mod_add by lia;exact Al).
 set (va:=ymm (mem s) a);set (vb:=ymm (mem s) b).
 set (u0:=set (set s 7 a) 6 b).
 set (u1:=CPU (regs u0) (fun k=>put (vectors u0 k) 0 (va k)) (flag u0) (mem u0)).
 set (u2:=CPU (regs u1) (fun k=>put (vectors u1 k) 1 (vb k)) (flag u1) (mem u1)).
 set (w0:=Store (word(slide+common+93)) d 32 (vector_byte (fun k=>vectors u2 k 0%nat))).
 set (w1:=Store (word(slide+common+98)) (d+256) 32 (vector_byte (fun k=>vectors u2 k 1%nat))).
 exists (with_words u2 (regs u2) (commit (commit (mem s) w0) w1)),[w0;w1];split.
 - apply (checked _ _ _ (proj1(proj2 code))).
   cbn [copies follow loc cpu_state cf step option_map set set_regs effective regs mem vectors put Nat.eqb with_words].
   rewrite Row,BX,Off,!Z.mul_1_r,!Z.add_0_r.
   repeat match goal with |-context[word ?x]=>rewrite (word_fits x ltac:(unfold word64 in *;lia)) end.
   rewrite First. replace (table+8*Z.of_nat j+64) with (table+64+8*Z.of_nat j) by ring.
   rewrite Second. repeat rewrite Z.add_0_r;rewrite ?(word_fits a A),?(word_fits b B).
   fold d;rewrite Al;change (0=?0) with true;cbn [step loc cpu_state cf option_map effective mem regs vectors with_words set set_regs put Nat.eqb].
   rewrite BX,Off,Z.mul_1_r;fold d;rewrite (word_fits (d+256)) by (unfold d,word64;lia).
   rewrite Ah;reflexivity.
 - split;[exact (conj SP (conj BX (conj Mask (conj Row Off))))|split;[reflexivity|]].
   constructor;[|constructor;[|constructor]];intros x X;unfold touches,w0,w1 in X;cbn [address size] in X;unfold d in *;lia.
Qed.

Definition loop_pc j := if (j=?8)%nat then 122 else 78.
Lemma advanced slide frame dst table mask j s c : (j<8)%nat -> fits64 table 128 ->
 holds frame dst table mask j s ->
 exists t cf,run 4 (run_common slide) (State (Running 107) s c)=Some(State (Running (loop_pc (S j))) t cf,[]) /\
 holds frame dst table mask (S j) t /\ mem t=mem s.
Proof.
 intros J [T V] [SP [BX [Mask [Row Off]]]].
 assert (G:word (regs s 15%nat)=table+8*Z.of_nat j) by (rewrite Row;apply word_fits;unfold word64;lia).
 assert (Next:word (table+8*Z.of_nat j+8)=table+8*Z.of_nat(S j)) by (rewrite word_fits;unfold word64;lia).
 assert (I:regs s 1%nat mod 2^32=32*Z.of_nat j) by (rewrite Off;apply Z.mod_small;lia).
 assert (N:(32*Z.of_nat j+32) mod 2^32=32*Z.of_nat(S j)) by (rewrite Z.mod_small;lia).
 assert (NI:(32*Z.of_nat(S j)) mod 2^32=32*Z.of_nat(S j)) by (apply Z.mod_small;lia).
 assert (EQ:(32*Z.of_nat(S j)=?256)=(S j=?8)%nat) by
   (destruct (Z.eqb_spec (32*Z.of_nat(S j)) 256),(Nat.eqb_spec (S j) 8);auto;lia).
 assert (Choice:(if negb (32*Z.of_nat(S j)=?256) then 78 else 122)=loop_pc (S j)).
 { unfold loop_pc;rewrite EQ;destruct (S j=?8)%nat;reflexivity. }
 do 2 eexists;split.
 - apply (checked _ _ _ (proj1(proj2(proj2 code)))).
   cbn [increment follow loc cf cpu_state step option_map eval_condition with_zf flag regs set set_regs put Nat.eqb].
   change (32 mod 2^32) with 32;change (256 mod 2^32) with 256.
   rewrite I,N,NI,<-Choice;reflexivity.
 - unfold holds;cbn [increment follow loc cf cpu_state step option_map eval_condition with_zf flag regs set set_regs put Nat.eqb mem].
   change (32 mod 2^32) with 32;change (word 8) with 8;rewrite ?G,?Next,?I,?N;repeat split;assumption || reflexivity.
Qed.

Definition dest dst j (sig:bool) := dst+32*Z.of_nat j+(if sig then 256 else 0).
Definition table_view m table (ptr:nat->bool->Z) := forall j (sig:bool),(j<8)%nat ->
 read_word m (table+(if sig then 64 else 0)+8*Z.of_nat j)=ptr j sig.
Definition source_view (original m:bytes) (ptr:nat->bool->Z) := forall j sig k,(j<8)%nat -> 0<=k<32 -> m(ptr j sig+k)=original(ptr j sig+k).
Definition staged (original m:bytes) dst (ptr:nat->bool->Z) lanes := forall j sig k,(j<lanes)%nat -> 0<=k<32 ->
 m(dest dst j sig+k)=original(ptr j sig+k).

Lemma fill slide frame dst table mask original ptr : fits64 dst 512 -> dst mod 32=0 ->
 fits64 table 128 -> disjoint dst 512 table 128 ->
 (forall j (sig:bool),(j<8)%nat -> fits64 (ptr j sig) 32 /\ disjoint dst 512 (ptr j sig) 32) ->
 forall fuel j s c,(fuel+j=8)%nat -> holds frame dst table mask j s -> byte_memory(mem s) ->
 table_view (mem s) table ptr -> source_view original (mem s) ptr -> staged original (mem s) dst ptr j ->
 exists t cf ws,run (10*fuel) (run_common slide) (State (Running (loop_pc j)) s c)=Some(State (Running 122) t cf,ws) /\
 holds frame dst table mask 8 t /\ staged original (mem t) dst ptr 8 /\ confined (fun x=>dst<=x<dst+512) ws.
Proof.
 intros D Align T Sep Range fuel;induction fuel as [|fuel IH];intros j s c Count G B Tab Orig Done.
 - replace j with 8%nat in * by lia;do 3 eexists;split;[reflexivity|split;[exact G|split;[exact Done|constructor]]].
 - assert (J:(j<8)%nat) by lia.
   pose proof(Range j false J) as [[AL AU] _];pose proof(Range j true J) as [[BL BU] _].
   pose proof(Tab j false J) as Key;cbn in Key;rewrite Z.add_0_r in Key.
   destruct(copy_pair slide frame dst table mask j s c (ptr j false) (ptr j true) G J Align D T
     ltac:(unfold word64;lia) ltac:(unfold word64;lia) Key (Tab j true J)) as [u [w [Copy [Held [Pair W]]]]].
   destruct(advanced slide frame dst table mask j u c J T Held) as [v [cv [Advance [Next Flat]]]].
   pose proof (run_append _ _ _ _ _ Copy _ _ _ Advance) as One;rewrite app_nil_r in One.
   assert (Byte:byte_memory(mem v)).
   { rewrite Flat,Pair;unfold pair_memory;repeat apply write_bytes_well_formed;auto;intros;apply Z.mod_pos_bound;lia. }
   assert (Out:forall x,~(dst<=x<dst+512) -> mem v x=mem s x).
   { intros x X;rewrite Flat,Pair;apply pair_out;lia. }
   assert (Tab':table_view (mem v) table ptr).
   { intros i sig R;rewrite <- (Tab i sig R);apply preserved_read with (outside:=fun x=>~(dst<=x<dst+512)).
     - exact Out.
     - intros k K;change (0<=k<8) in K;destruct sig;unfold disjoint in Sep;lia. }
   assert (Orig':source_view original (mem v) ptr).
   { intros i sig k R K;rewrite Out;[apply Orig;assumption|destruct (Range i sig R) as [_ Apart];unfold disjoint in Apart;lia]. }
   assert (Done':staged original (mem v) dst ptr (S j)).
   { intros i sig k R K;rewrite Flat,Pair;unfold dest. destruct (Nat.eq_dec i j) as [->|Ne].
     - rewrite pair_at by assumption. destruct sig;apply Orig;assumption.
     - rewrite pair_out;[apply Done;lia|destruct sig;lia|destruct sig;lia]. }
   destruct (IH (S j) v cv ltac:(lia) Next Byte Tab' Orig' Done') as [endst [flags [tail [R [H [Data Safe]]]]]].
   exists endst,flags,(w++tail);split;[|split;[exact H|split;[exact Data|apply Forall_app;auto]]].
   unfold loop_pc at 1;rewrite (proj2 (Nat.eqb_neq j 8) ltac:(lia)).
   replace (10*S fuel)%nat with (10+10*fuel)%nat by lia.
   exact (run_append _ 10 _ _ _ One _ _ _ R).
Qed.

Lemma dispatch slide s c frame dst mask table :
 holds frame dst table mask 8 s -> fits64 dst 3584 -> word64(frame-8) -> word64(slide+decoder) ->
 exists t ws,run 4 (run_common slide) (State (Running 122) s c)=Some(t,ws) /\
 loc t=Running (decoder-common) /\ regs(cpu_state t) 7%nat=dst+1024 /\ regs(cpu_state t) 6%nat=dst /\
 regs(cpu_state t) 2%nat=2 /\ regs(cpu_state t) 4%nat=frame-8 /\
 read_word (mem(cpu_state t)) (frame-8)=word(slide+common+142) /\
 confined (fun x=>frame-8<=x<frame) ws.
Proof.
 intros [SP [BX _]] [L U] Slot Target.
 eexists; eexists;split;[apply (checked _ _ _ (proj2(proj2(proj2 code))));reflexivity|].
 cbn [call follow loc cf cpu_state step option_map regs mem set set_regs put Nat.eqb effective
      push push_words apply_stack caller_step next_pc encoding stack_step result_regs result_mem target_ip fst snd].
 rewrite SP,BX,!Z.add_0_r,(word_fits _ Slot).
 replace (slide+common+(137+Z.of_nat 5+(decoder-(common+142)))) with (slide+decoder) by ring.
 rewrite (word_fits _ Target);rewrite (word_fits (dst+1024)),(word_fits dst) by (unfold word64;lia).
 split;[f_equal;ring|]. do 4 (split;[reflexivity|]);split.
 - apply read_word_encoded;intros k K;apply write_at,K.
 - constructor;[|constructor];intros x X;exact X || (change (frame-8<=x<frame-8+8) in X;lia).
Qed.

Definition handed slide frame dst original ptr t :=
 loc t=Running (decoder-common) /\ regs(cpu_state t) 7%nat=dst+1024 /\ regs(cpu_state t) 6%nat=dst /\
 regs(cpu_state t) 2%nat=2 /\ regs(cpu_state t) 4%nat=frame-8 /\
 read_word (mem(cpu_state t)) (frame-8)=word(slide+common+142) /\ staged original (mem(cpu_state t)) dst ptr 8.

Theorem to_decoder slide frame dst table original ptr s c :
 regs s 0%nat mod 2^32<>0 -> regs s 4%nat=frame -> regs s 3%nat=dst -> regs s 15%nat=table ->
 fits64 dst 3584 -> dst mod 32=0 -> fits64 table 128 -> disjoint dst 512 table 128 ->
 word64(frame-8) -> word64(slide+decoder) -> disjoint (frame-8) 8 dst 512 ->
 (forall j (sig:bool),(j<8)%nat -> fits64 (ptr j sig) 32 /\ disjoint dst 512 (ptr j sig) 32) ->
 byte_memory (mem s) -> table_view (mem s) table ptr -> source_view original (mem s) ptr ->
 exists t ws,run 88 (run_common slide) (State (Running 65) s c)=Some(t,ws) /\
 handed slide frame dst original ptr t /\ confined (fun x=>dst<=x<dst+512 \/ frame-8<=x<frame) ws /\
 regs(cpu_state t) 13%nat=regs s 13%nat /\ regs(cpu_state t) 14%nat=regs s 0%nat mod 2^32 /\ regs(cpu_state t) 3%nat=dst /\ regs(cpu_state t) 12%nat=regs s 12%nat.
Proof.
 intros Nonzero SP BX R15 Fit Al Table Apart Stack Target Sep Inputs Bytes Ptr Original.
 destruct(started slide s c frame dst table Nonzero SP BX R15) as [u [Start [Held M]]].
 destruct(fill slide frame dst table _ original ptr ltac:(unfold fits64 in *;lia) Al Table Apart Inputs
   8 0 u (Some false) eq_refl Held ltac:(now rewrite M) ltac:(unfold table_view;now rewrite M)
   ltac:(unfold source_view;now rewrite M) ltac:(intros j b k J;lia))
   as [v [cv [body [Copies [V [Data W]]]]]].
 destruct(dispatch slide v cv frame dst _ table V Fit Stack Target) as [t [tail [Call [IP [DI [SI [DX [Top [Ret Safe]]]]]]]]].
 assert (Sel:forall r,r=12%nat \/ r=13%nat -> regs(cpu_state t) r=regs s r).
 { intros r Index;pose proof(PreservedRegister.run_keeps_at r _ CommonBytes.symbol_bytes ltac:(vm_compute;reflexivity) 4 65 _ _ _ _ ltac:(destruct Index as [->| ->];vm_compute;reflexivity) Start) as H.
   pose proof(PreservedRegister.run_keeps_at r _ CommonBytes.symbol_bytes ltac:(vm_compute;reflexivity) 80 78 _ _ _ _ ltac:(destruct Index as [->| ->];vm_compute;reflexivity) Copies) as M'.
   pose proof(PreservedRegister.run_keeps_at r _ CommonBytes.symbol_bytes ltac:(vm_compute;reflexivity) 4 122 _ _ _ _ ltac:(destruct Index as [->| ->];vm_compute;reflexivity) Call) as E.
   exact (eq_trans E (eq_trans M' H)). }
 assert (Mask:regs(cpu_state t) 14%nat=regs s 0%nat mod 2^32) by
   (rewrite (PreservedRegister.run_keeps_at 14 _ CommonBytes.symbol_bytes ltac:(vm_compute;reflexivity) 4 122 _ _ _ _ ltac:(vm_compute;reflexivity) Call);exact (proj1(proj2(proj2 V)))).
 assert (Scratch:regs(cpu_state t) 3%nat=dst) by
   (rewrite (PreservedRegister.run_keeps_at 3 _ CommonBytes.symbol_bytes ltac:(vm_compute;reflexivity) 4 122 _ _ _ _ ltac:(vm_compute;reflexivity) Call);exact (proj1(proj2 V))).
 exists t,(body++tail);split.
 - exact (run_append _ 84 _ _ _ (run_append _ 4 _ _ _ Start 80 _ _ Copies) 4 _ _ Call).
 - split;[|split;[|exact (conj (Sel 13%nat (or_intror eq_refl)) (conj Mask (conj Scratch (Sel 12%nat (or_introl eq_refl)))))];apply Forall_app;split;eapply Forall_impl;[|exact W| |exact Safe];intros w H x X;auto].
   unfold handed;repeat (split;[assumption|]). intros j sig k J K;rewrite <- (Data j sig k J K).
   pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Call)) as M'.
   cbn [cpu_state] in M';rewrite M';apply (WriteTrace.frame _ _ Safe).
   unfold dest,disjoint in *;destruct sig;lia.
Qed.
