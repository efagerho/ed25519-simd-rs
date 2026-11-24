From Coq Require Import ZArith List Lia.
From Machine Require Import isa.Instructions isa.IndexedLoad isa.VectorMoves isa.QwordRegister
 execution.LinkedCalls execution.ScalarBytes execution.WordSemantics execution.WordBounds
 execution.InstructionRoute execution.MappedFetch memory.MemoryGeometry memory.ByteMemory.
From Ed25519Simd.VerifyBatch Require Import DescriptorStores.
From Ed25519Simd.VerifyBatch Require DecoderFrame.
Import ListNotations. Local Open Scope Z_scope.

Definition words : list IndexedLoad.instruction :=
 map (fun i=>LoadZ i (Addr 6 false (64*Z.of_nat i))) (seq 0 4) ++
 [ShuffleWords 4 0 1 136;ShuffleWords 5 2 3 136;ShuffleWords 6 0 1 221;ShuffleWords 7 2 3 221].
Definition tables : list line := [(299,10%nat,QwordOp(AlignedRip 8 (0xb00-309)));
                                    (309,10%nat,QwordOp(AlignedRip 9 (0xb40-319)))].
Definition permutes : list line :=
 [(319,6%nat,QwordOp(Alu(0%nat,Instructions.Copy 4)));(325,6%nat,QwordOp(Permute2 0 8 5));
  (331,6%nat,QwordOp(Permute2 4 9 5));(337,6%nat,QwordOp(Alu(2%nat,Instructions.Copy 6)));
  (343,6%nat,QwordOp(Permute2 2 8 7));(349,6%nat,QwordOp(Permute2 6 9 7))].
Lemma linked_words : FrameInstructions.decoded DecoderFrame.code 244 (map input words).
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma linked_tables : linked DecoderFrame.code tables.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Lemma linked_permutes : linked DecoderFrame.code permutes.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Definition row_index (r j:nat) := (8*((r mod 2)*2+j/4)+2*((if r<?6 then 2*(j/2 mod 2) else 1+2*(j/2 mod 2)))+j mod 2)%nat.
Definition word_at s i := read_word (mem s) (word(regs s 6%nat+64*Z.of_nat(i/8))+8*Z.of_nat(i mod 8)).
Lemma shuffled s r j : (4<=r<8)%nat -> (j<8)%nat ->
 vectors (load_vectors words s) j r=word_at s (row_index r j).
Proof.
 intros R J;do 4 (destruct r as [|r];[lia|]).
 do 4 (destruct r as [|r];[do 8 (destruct j as [|j];[reflexivity|]);lia|]);lia.
Qed.
Definition index_addr o odd := o+0xb00+(if odd:bool then 64 else 0).
Definition index_word o m odd j := read_word m (index_addr o odd+8*Z.of_nat j).
Definition even_odd s := forall j,(j<8)%nat -> vectors s j 8%nat=2*Z.of_nat j /\ vectors s j 9%nat=2*Z.of_nat j+1.
Definition placed o := o mod 64=0 /\ word64(index_addr o false) /\ word64(index_addr o true).
Definition literal_values o m := forall (odd:bool) j,(j<8)%nat ->
 index_word o m odd j=2*Z.of_nat j+(if odd then 1 else 0).

Lemma literal_addresses o : placed o -> forall odd,word(index_addr o odd)=index_addr o odd /\ index_addr o odd mod 64=0.
Proof.
 intros [Al [Even Odd]] [];split;try (apply word_fits;assumption);
 unfold index_addr;replace (o+0xb00+64) with (o+45*64) by ring;replace (o+0xb00+0) with (o+44*64) by ring;now rewrite Z.mod_add by lia.
Qed.
Lemma load_tables o s c : placed o -> literal_values o (mem s) ->
 exists t,run 2 (ScalarBytes.fetch o DecoderFrame.code) (State (Running 299) s c)=Some(State (Running 319) t c,[]) /\
 even_odd t /\ (forall j r,r<>8%nat -> r<>9%nat -> vectors t j r=vectors s j r) /\ mem t=mem s /\ regs t=regs s.
Proof.
 intros P L;destruct(literal_addresses o P false) as [EF EA];destruct(literal_addresses o P true) as [OF OA].
 set (load:=fun s r odd=>vector_dest s r (index_word o (mem s) odd)).
 exists (load (load s 8%nat false) 9%nat true);split.
 - apply (checked _ _ _ linked_tables);cbn [tables follow loc cpu_state cf step qword_op option_map].
   replace (o+(299+Z.of_nat 10)+(0xb00-309)) with (index_addr o false) by (unfold index_addr;ring).
   rewrite EF,EA;cbn [option_map tables follow loc cpu_state cf step qword_op].
   replace (o+(309+Z.of_nat 10)+(0xb40-319)) with (index_addr o true) by (unfold index_addr;ring).
   rewrite OF,OA;reflexivity.
 - split.
   + intros j J;split;[change (index_word o (mem s) false j=2*Z.of_nat j);rewrite L by exact J;ring|
       exact (L true j J)].
   + split;[intros j r R8 R9;unfold load,vector_dest;cbn [vectors];unfold put;
       rewrite (proj2(Nat.eqb_neq 9 r) ltac:(lia)),(proj2(Nat.eqb_neq 8 r) ltac:(lia));reflexivity|split;reflexivity].
Qed.

Definition result_reg w := nth w [0;4;2;6]%nat 0%nat.
Definition selected w j := (2*j+w mod 2)%nat.
Definition source_reg w j := (4+2*(w/2)+(selected w j)/8)%nat.

Lemma pick o s c : even_odd s ->
 exists v,run 6 (ScalarBytes.fetch o DecoderFrame.code) (State (Running 319) s c)=Some(State (Running 355) v c,[]) /\
 mem v=mem s /\ regs v=regs s /\ (forall j,vectors v j 29%nat=vectors s j 29%nat) /\ forall j w,(j<8)%nat -> (w<4)%nat ->
 vectors v j (result_reg w)=vectors s ((selected w j) mod 8)%nat (source_reg w j).
Proof.
 intros E;assert (Even:forall j,(j<8)%nat -> vectors s j 8%nat=2*Z.of_nat j) by (intros;apply E;assumption).
 assert (Odd:forall j,(j<8)%nat -> vectors s j 9%nat=2*Z.of_nat j+1) by (intros;apply E;assumption).
 eexists;split;[apply (checked _ _ _ linked_permutes);reflexivity|].
 split;[reflexivity|split;[reflexivity|]].
 split;[intros j;reflexivity|]. intros j w J W;destruct w as [|[|[|[|w]]]];try lia;
 do 8 (destruct j as [|j];[shelve|]);try lia. Unshelve.
 all: cbn [result_reg nth permutes follow loc cf cpu_state step qword_op vector_dest bits option_map
   vectors put Nat.eqb fst snd Move.copy].
 all: unfold put,Move.copy;cbn [Nat.eqb].
 all: repeat first [rewrite Even by (lia || match goal with |- (Z.to_nat (?x mod 8)<8)%nat =>
                 pose proof(Z.mod_pos_bound x 8 ltac:(lia));lia end)
                  |rewrite Odd by (lia || match goal with |- (Z.to_nat (?x mod 8)<8)%nat =>
                 pose proof(Z.mod_pos_bound x 8 ltac:(lia));lia end)
                  |progress cbn [Nat.eqb]];reflexivity.
Qed.

Lemma read_words o s c : placed o -> literal_values o (mem s) ->
 exists v,run 16 (ScalarBytes.fetch o DecoderFrame.code) (State (Running 244) s c)=Some(State (Running 355) v c,[]) /\
 mem v=mem s /\ regs v=regs s /\ (forall j,vectors v j 29%nat=vectors s j 29%nat) /\ forall j w,(j<8)%nat -> (w<4)%nat ->
 vectors v j (result_reg w)=word_at s (4*j+w)%nat.
Proof.
 intros P L;pose proof(read_block o DecoderFrame.code words 244 s c ltac:(lia) linked_words) as W.
 set (mid:=load_vectors words s) in *.
 change (run 8 (ScalarBytes.fetch o DecoderFrame.code) (State (Running 244) s c)=Some(State (Running 299) mid c,[])) in W.
 destruct (load_tables o mid c P L) as [t [T [E [Rows [MT RT]]]]].
 destruct(pick o t c E) as [v [V [MV [RV [C29 Data]]]]].
 pose proof(run_append _ _ _ _ _ (run_append _ _ _ _ _ W _ _ _ T) _ _ _ V) as Run.
 exists v;split;[exact Run|]. split;[now rewrite MV,MT|split;[now rewrite RV,RT|]].
 split;[intros j;rewrite C29,Rows by lia;reflexivity|]. intros j w J H;rewrite Data by assumption. assert (R:(4<=source_reg w j<8)%nat).
 { do 4 (destruct w as [|w];[do 8 (destruct j as [|j];[vm_compute;lia|]);lia|]);lia. }
 rewrite Rows by lia;unfold mid;rewrite shuffled by (lia || apply Nat.mod_upper_bound;lia).
 f_equal;do 4 (destruct w as [|w];[do 8 (destruct j as [|j];[reflexivity|]);lia|]);lia.
Qed.

Definition at_index odd j := 0xb00+(if odd:bool then 64 else 0)+8*Z.of_nat j.
Lemma index_image odd j : (j<8)%nat ->
 read_word (fun x=>nth (Z.to_nat x) DecoderFrame.code 0) (at_index odd j)=
   2*Z.of_nat j+(if odd then 1 else 0).
Proof. intro J;destruct odd;do 8 (destruct j as [|j];[vm_compute;reflexivity|]);lia. Qed.

Lemma mapped_indices m o : o mod 64=0 -> fits64 o (Z.of_nat(length DecoderFrame.code)) ->
 mapped m o DecoderFrame.code -> placed o /\ literal_values o m.
Proof.
 intros Al [Lo Hi] Map;change (Z.of_nat(length DecoderFrame.code)) with 2984 in Hi.
 split;[split;[exact Al|unfold word64,index_addr;split;lia]|].
 intros odd j J;unfold index_word,index_addr;rewrite <- (index_image odd j J).
 replace (o+0xb00+(if odd then 64 else 0)+8*Z.of_nat j) with (o+at_index odd j)
    by (unfold at_index;ring).
 apply DecoderFrame.literal_read;[exact Map|unfold at_index;destruct odd;lia|
  change (Z.of_nat(length DecoderFrame.code)) with 2984;unfold at_index;destruct odd;lia].
Qed.

Lemma contiguous s base j w : regs s 6%nat=base -> fits64 base 256 -> (j<8)%nat -> (w<4)%nat ->
 word_at s (4*j+w)%nat=read_word (mem s) (base+32*Z.of_nat j+8*Z.of_nat w).
Proof.
 intros SI [Lo Hi] J W;unfold word_at;rewrite SI;set (i:=(4*j+w)%nat).
 pose proof(Nat.div_mod i 8 ltac:(lia));pose proof(Nat.mod_upper_bound i 8 ltac:(lia)).
 assert (I:(i<32)%nat) by (unfold i;lia).
 rewrite word_fits by (unfold word64;lia);f_equal;unfold i in *;lia.
Qed.
