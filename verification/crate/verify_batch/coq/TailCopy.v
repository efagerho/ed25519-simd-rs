From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute
 memory.FlatMemory memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Image Rows Return TailWrites.
Import ListNotations. Local Open Scope Z_scope.

Definition copy : list line :=
 [(639,4%nat,LoadY 0 (Address 6 None 0));(643,4%nat,Load64 0 (Address 6 None 32));
  (647,5%nat,StoreY 0 (Address 3 (Some (1%nat,1)) 0));
  (652,5%nat,Store64 0 (Address 3 (Some (1%nat,1)) 32))].
Definition advance : list line :=
 [(657,4%nat,LeaG 0 (Address 6 None 40));(661,3%nat,Compare 6 7);
  (664,4%nat,MoveBelow 6 0);(668,3%nat,Add32 1 40);
  (671,6%nat,Compare32 1 320);(677,2%nat,Branch ScalarBytes.Unequal (-40))].
Lemma linked_body text : TailWrites.bound text -> linked text copy /\ linked text advance.
Proof.
 intros B;unfold TailWrites.bound,TailWrites.listing in B.
 do 10 (let H:=fresh in apply Forall_cons_iff in B as [H B];cbv beta iota in H).
 repeat constructor;try discriminate;assumption.
Qed.

Definition copy_bytes m a dst :=
 let low:=fun j=>if (j<?4)%nat then read_word m (a+8*Z.of_nat j) else 0 in
 store_word (write_bytes m dst 32 (vector_byte low)) (dst+32) (read_word m (a+32)).
Definition held frame src last j s :=
 regs s 3%nat=frame /\ regs s 1%nat=40*Z.of_nat j /\ regs s 6%nat=src /\ regs s 7%nat=last.
Lemma copied o text frame src last j s c : linked text copy -> held frame src last j s ->
 fits64 src 40 -> fits64 (frame+40*Z.of_nat j) 40 ->
 exists u w,run 4 (ScalarBytes.fetch o text) (State (Running 639) s c)=Some(State (Running 657) u c,w) /\
 held frame src last j u /\ mem u=copy_bytes (mem s) src (frame+40*Z.of_nat j).
Proof.
 intros Code [Base [Off [Src Last]]] [L H] [D U]. do 2 eexists;split;[apply (checked _ _ _ Code);reflexivity|].
 split;[exact (conj Base (conj Off (conj Src Last)))|].
 cbn [copy follow loc cpu_state cf option_map step effective set set_regs regs vectors put Nat.eqb mem with_words].
 rewrite Src,Base,Off,Z.mul_1_r,!Z.add_0_r.
 repeat match goal with |-context[word ?a]=>rewrite (word_fits a ltac:(unfold word64 in *;lia)) end.
 reflexivity.
Qed.

Lemma copied_value m a dst k : byte_memory m -> 0<=k<40 -> copy_bytes m a dst (dst+k)=m(a+k).
Proof.
 intros B K;unfold copy_bytes,store_word. destruct(Z_lt_ge_dec k 32) as [Low|High].
 - rewrite write_outside by lia;rewrite write_at by lia;unfold vector_byte.
   assert (Q:0<=k/8<4) by (split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia).
   rewrite (proj2 (Nat.ltb_lt (Z.to_nat(k/8)) 4) ltac:(lia)),Z2Nat.id by lia.
   rewrite read_word_byte by (try exact B;apply Z.mod_pos_bound;lia).
   f_equal;pose proof(Z.div_mod k 8 ltac:(lia));lia.
 - replace (dst+k) with (dst+32+(k-32)) by ring;rewrite write_at by lia.
   rewrite read_word_byte by (auto;lia);f_equal;ring.
Qed.
Lemma copied_outside m a dst x : ~(dst<=x<dst+40) -> copy_bytes m a dst x=m x.
Proof. intro Away;unfold copy_bytes,store_word;rewrite !write_outside by lia;reflexivity. Qed.

Definition source base n j := base+40*Z.min (Z.of_nat j) (n-1).
Definition last base n := base+40*(n-1).
Definition finish_pc j := if (S j=?8)%nat then 679 else 639.
Lemma counted o text frame base n j s c :
 linked text advance -> (j<8)%nat -> 1<=n<=8 -> fits64 base (40*n) ->
 held frame (source base n j) (last base n) j s ->
 exists t cf,run 6 (ScalarBytes.fetch o text) (State (Running 657) s c)=Some(State (Running (finish_pc j)) t cf,[]) /\
 held frame (source base n (S j)) (last base n) (S j) t /\ mem t=mem s.
Proof.
 intros Code J N [L U] [Base [Off [Src Last]]].
 set (a:=source base n j) in *;set (endp:=last base n) in *.
 assert (A:word a=a) by (apply word_fits;unfold a,source,word64;lia).
 assert (E:word endp=endp) by (apply word_fits;unfold endp,last,word64;lia).
 assert (Next:(if a<?endp then word(a+40) else a)=source base n (S j)).
 { unfold a,endp,source,last. rewrite Nat2Z.inj_succ.
   destruct(Z.ltb_spec (base+40*Z.min (Z.of_nat j) (n-1)) (base+40*(n-1))).
   - rewrite word_fits by (unfold word64;lia);lia.
   - lia. }
 assert (Added:(40*Z.of_nat j mod 2^32+40 mod 2^32) mod 2^32=40*Z.of_nat(S j)).
 { change (40 mod 2^32) with 40;rewrite (Z.mod_small (40*Z.of_nat j) (2^32)) by lia;rewrite Z.mod_small by lia;lia. }
 assert (Branch:(if negb (40*Z.of_nat(S j)=?320) then 639 else 679)=finish_pc j).
 { unfold finish_pc;destruct(Nat.eqb_spec (S j) 8);[subst;rewrite (proj2(Z.eqb_eq (40*Z.of_nat(S j)) 320) ltac:(lia))|
     rewrite (proj2(Z.eqb_neq (40*Z.of_nat(S j)) 320) ltac:(lia))];reflexivity. }
 destruct(a<?endp) eqn:Before.
 all: do 2 eexists;split.
 1,3: apply (checked _ _ _ Code);
   cbn [advance follow loc cpu_state cf option_map eval_condition step effective set with_zf set_regs regs flag put Nat.eqb];
   rewrite Src,Last,A,E,Before;cbn [regs flag with_zf set set_regs put Nat.eqb];rewrite Off,Added;rewrite (Z.mod_small (40*Z.of_nat(S j)) (2^32)) by lia;
   change (320 mod 2^32) with 320;rewrite <-Branch;reflexivity.
 all: cbn [regs mem with_zf set set_regs put Nat.eqb effective] in *;unfold held;cbn [regs mem with_zf set set_regs put Nat.eqb effective].
 all: rewrite ?Src,?Last,?Off,?Z.add_0_r,?Added;repeat split;assumption || reflexivity.
Qed.

Definition intact original frame base n j s :=
 byte_memory (mem s) /\
 (forall x,base<=x<base+40*n -> mem s x=original x) /\
 forall i k,(i<j)%nat -> 0<=k<40 -> mem s (frame+40*Z.of_nat i+k)=original (source base n i+k).

Lemma fill o text original frame base n :
 TailWrites.bound text -> 1<=n<=8 -> fits64 base (40*n) -> fits64 frame 320 ->
 disjoint frame 320 base (40*n) ->
 forall fuel j s c,(fuel+j=8)%nat -> held frame (source base n j) (last base n) j s ->
 intact original frame base n j s ->
 exists t cf ws,run (10*fuel) (ScalarBytes.fetch o text)
  (State (Running (if (j=?8)%nat then 679 else 639)) s c)=Some(State (Running 679) t cf,ws) /\
 regs t 3%nat=frame /\ intact original frame base n 8 t /\
 preserved (fun x=>~(frame<=x<frame+320)) (mem s) (mem t).
Proof.
 intros Code N Fits Frame Sep;destruct(linked_body _ Code) as [Copies Control].
 induction fuel as [|fuel IH];intros j s c Left Regs [Bytes [Input Rows]].
 - replace j with 8%nat in * by lia;do 3 eexists;split;[reflexivity|].
   split;[exact (proj1 Regs)|split;[exact (conj Bytes (conj Input Rows))|intros x _;reflexivity]].
 - assert (J:(j<8)%nat) by lia.
   rewrite (proj2 (Nat.eqb_neq j 8) ltac:(lia)).
   set (a:=source base n j) in *;set (dst:=frame+40*Z.of_nat j).
   assert (Src:base<=a /\ a+40<=base+40*n) by (unfold a,source;lia).
   assert (D:frame<=dst /\ dst+40<=frame+320) by (unfold dst;lia).
   destruct (copied o text frame a (last base n) j s c Copies Regs
     ltac:(unfold fits64 in *;lia) ltac:(fold dst;unfold fits64 in *;lia)) as [u [own [Copy [U M]]]].
   destruct (counted o text frame base n j u c Control J N Fits U)
     as [v [flags [Advance [V Flat]]]].
   assert (StateV:intact original frame base n (S j) v).
   { unfold intact;rewrite Flat,M;fold dst. split.
     - intro x;destruct(Z_le_dec dst x), (Z_lt_dec x (dst+40));
       try (rewrite copied_outside by lia;apply Bytes).
       replace x with (dst+(x-dst)) by ring;rewrite copied_value by (auto;lia);apply Bytes.
     - split.
       + intros x X;rewrite copied_outside by (unfold disjoint in Sep;lia);apply Input,X.
       + intros i k I K;destruct(Nat.eq_dec i j) as [->|Earlier].
         * fold dst;rewrite copied_value by assumption;apply Input;lia.
         * rewrite copied_outside by (unfold dst;lia);apply Rows;lia. }
   destruct (IH (S j) v flags ltac:(lia) V StateV) as [t [cf [tail [Rest [End [Values Outside]]]]]].
   exists t,cf,(own++tail);split;[|split;[exact End|split;[exact Values|]]].
   2:{ intros x X;rewrite Outside by exact X;rewrite Flat,M;apply copied_outside;unfold dst in *;lia. }
   pose proof(run_append _ _ _ _ _ Copy _ _ _ Advance) as One;rewrite app_nil_r in One.
   replace (10*S fuel)%nat with (10+10*fuel)%nat by lia.
   eapply run_append;[exact One|exact Rest].
Qed.

Definition start : list line :=
 [(56,4%nat,CompareImm 12 8);(60,6%nat,Branch ScalarBytes.Below (610-66));(610,8%nat,Store64 12 (Address 4 None 928));
  (618,3%nat,CopyG 6 3);(621,4%nat,LeaG 0 (Address 12 (Some (12%nat,4)) 0));
  (625,5%nat,LeaG 7 (Address 3 (Some (0%nat,8)) (-40)));(630,4%nat,LeaG 3 (Address 4 None 0));
  (634,3%nat,Zero32 12);(637,2%nat,Zero32 1)].
Definition jump : list line := [(679,5%nat,ScalarBytes.Jump (82-684))].

Lemma started o text frame base n s c : linked text start -> 1<=n<8 ->
 fits64 base (40*n) -> fits64 frame 960 -> regs s 4%nat=frame ->
 regs s 3%nat=base -> regs s 12%nat=n ->
 exists u ws,run 9 (ScalarBytes.fetch o text) (State (Running 56) s c)=Some(State (Running 639) u (Some false),ws) /\
 held frame (source base n 0) (last base n) 0 u /\ mem u=store_word (mem s) (frame+928) n.
Proof.
 intros Code N [L U] [FL FU] SP BX Left.
 assert (W:word n=n) by (apply word_fits;unfold word64;lia).
 do 2 eexists;split.
 - apply (checked _ _ _ Code);
   cbn [start follow loc cf cpu_state eval_condition step regs with_zf flag option_map];rewrite Left,W.
   rewrite (proj2 (Z.ltb_lt n 8) ltac:(lia));reflexivity.
 - unfold held,source,last;cbn [start follow loc cf cpu_state eval_condition step regs with_zf flag option_map
     set set_regs put Nat.eqb mem with_words effective commit qword WriteTrace.address WriteTrace.size payload].
   rewrite SP,BX,Left. repeat match goal with |-context[word ?a]=>rewrite (word_fits a ltac:(unfold word64 in *;lia)) end.
   replace (Z.min (Z.of_nat 0) (n-1)) with 0 by lia. repeat split;try lia.
   rewrite Z.add_0_r;reflexivity.
Qed.
Lemma jumped o text s c : linked text jump ->
 run 1 (ScalarBytes.fetch o text) (State (Running 679) s c)=Some(State (Running 82) s c,[]).
Proof. intro Code;apply (checked _ _ _ Code);reflexivity. Qed.

Theorem staged o text frame base n original s c :
 linked text start -> linked text jump -> TailWrites.bound text ->
 1<=n<8 -> fits64 base (40*n) -> fits64 frame 960 -> disjoint frame 960 base (40*n) ->
 regs s 4%nat=frame -> regs s 3%nat=base -> regs s 12%nat=n -> byte_memory(mem s) ->
 (forall x,base<=x<base+40*n -> mem s x=original x) ->
 exists t cf ws,run 90 (ScalarBytes.fetch o text) (State (Running 56) s c)=Some(State (Running 82) t cf,ws) /\
 regs t 3%nat=frame /\ (forall i k,(i<8)%nat -> 0<=k<40 ->
 mem t (frame+40*Z.of_nat i+k)=original (source base n i+k)) /\ read_word (mem t) (frame+928)=n /\
 (forall x,frame+936<=x -> mem t x=mem s x).
Proof.
 intros Start Jump Body N Fit Frame Sep SP BX Left Bytes Borrow.
 destruct (started o text frame base n s c Start N Fit Frame SP BX Left) as [u [w [R [Held Store]]]].
 assert (I:intact original frame base n 0 u).
 { unfold intact;rewrite Store;split;[apply write_bytes_well_formed;auto using word_byte_bound|].
   split;[|intros;lia]. intros x X;unfold store_word;rewrite write_outside by (unfold disjoint in Sep;lia);apply Borrow,X. }
 destruct (fill o text original frame base n Body ltac:(lia) Fit ltac:(unfold fits64 in *;lia)
    ltac:(unfold disjoint in *;lia) 8 0 u (Some false) eq_refl Held I) as [t [cf [ws [Copy [Base [[_ [_ Data]] Outside]]]]]].
 exists t,cf,((w++ws)++[]);split;[|split;[exact Base|split;[exact Data|]]].
 2:{ split;[apply read_word_exact;[unfold word64;lia|intros k K;rewrite Outside by lia;rewrite Store;apply write_at,K]|].
     intros x X;rewrite Outside by lia;rewrite Store;unfold store_word;apply write_outside;lia. }
 exact (run_append _ _ _ _ _ (run_append _ 9 _ _ _ R 80 _ _ Copy) 1 _ _ (jumped o text t cf Jump)).
Qed.

Definition row_index e j := Nat.min j (Scatter.count e-1).
Lemma live_row e j : (0<Scatter.count e)%nat -> (row_index e j<Scatter.count e)%nat.
Proof. unfold row_index;lia. Qed.
Lemma own_row e j : (j<Scatter.count e)%nat -> row_index e j=j.
Proof. unfold row_index;intros;apply Nat.min_l;lia. Qed.
Lemma source_row e j : (0<Scatter.count e)%nat ->
 source (regs e 7%nat) (regs e 6%nat) j=regs e 7%nat+40*Z.of_nat(row_index e j).
Proof. unfold row_index,source,Scatter.count;intros;rewrite Nat2Z.inj_min,Nat2Z.inj_sub by lia.
 rewrite Z2Nat.id by lia;reflexivity. Qed.
