From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls
 execution.ScalarBytes execution.MappedFetch execution.InstructionRoute execution.StoreInstructions
 memory.FlatMemory memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.Zip215 Require ScatterBytes.
Import ListNotations. Local Open Scope Z_scope.

Definition begin : list line :=
 [(0,4%nat,Load64 1 (Address 7 None 72));(4,4%nat,CompareImm 1 8);(8,2%nat,Branch Above 45);
  (10,3%nat,Zero32 8);(13,3%nat,Test 1);(16,2%nat,Branch Equal 31)].
Definition guard : list line :=
 [(18,5%nat,Load64 9 (Address 7 (Some (8%nat,8)) 8));(23,3%nat,Compare 9 2);
  (26,2%nat,Branch AtLeast 27)].
Definition publish : list line :=
 [(28,4%nat,Load8 10 (Address 7 (Some (8%nat,1)) 0));(32,3%nat,And8 10 0);
  (35,4%nat,Store8 (IndexedByte 10 6 9));(39,2%nat,ShrEax);(41,3%nat,Inc 8);
  (44,3%nat,Compare 8 1);(47,2%nat,Branch Below (-31))].
Definition success : list line := [(49,5%nat,OneEax);(54,1%nat,Ret)].
Lemma bytes_bound : let code:=ScatterBytes.symbol_bytes in
 linked code begin /\ linked code guard /\ linked code publish /\ linked code success.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Definition fetch_at o := ScalarBytes.fetch o ScatterBytes.symbol_bytes.
Fixpoint remaining (mask:Z) (j:nat) := match j with
 | O=>mask | S i=>(remaining mask i mod 2^32)/2 end.
Definition verdict flags mask j:=Z.land (flags j mod 256) (remaining mask j mod 256) mod 256.
Definition args mask meta out len active j s := regs s 7%nat=meta /\ regs s 6%nat=out /\ regs s 2%nat=len /\
 regs s 0%nat=remaining mask j /\ regs s 8%nat=Z.of_nat j /\ regs s 1%nat=Z.of_nat active.
Definition index_address meta j := meta+8+8*Z.of_nat j.
Definition indices m meta n (idx:nat->Z) := forall j,(j<n)%nat -> read_word m (index_address meta j)=idx j.
Definition next active j := if (j<?active)%nat then 18 else 49.

Lemma start mask o s c meta out len active : (0<active<=8)%nat -> fits64 meta 80 ->
 regs s 7%nat=meta -> regs s 6%nat=out -> regs s 2%nat=len -> regs s 0%nat=mask ->
 read_word (mem s) (meta+72)=Z.of_nat active ->
 exists t,run 6 (fetch_at o) (State (Running 0) s c)=Some(State (Running 18) t (Some false),[]) /\
 args mask meta out len active 0 t /\ mem t=mem s.
Proof.
 intros N [L H] Source Dst Len AX Count. set (n:=Z.of_nat active) in *.
 assert (W:word n=n) by (apply word_fits;unfold n,word64;lia).
 assert (A:negb ((n=?8)||(n<?8))=false) by
  (unfold n;destruct (Z.eqb_spec (Z.of_nat active) 8),(Z.ltb_spec (Z.of_nat active) 8);cbn;try reflexivity;lia).
 assert (B:(n=?0)=false) by (apply Z.eqb_neq;unfold n;lia).
 eexists;split.
 - apply (checked _ _ _ (proj1 bytes_bound)).
   cbn [begin follow loc cf cpu_state eval_condition step option_map effective set set_regs with_zf flag regs put Nat.eqb].
   rewrite Source,Z.add_0_r,(word_fits (meta+72)) by (unfold word64;lia).
   rewrite Count,W,A,B;reflexivity.
 - unfold args;cbn [begin follow loc cf cpu_state eval_condition step option_map effective set set_regs with_zf flag regs mem put Nat.eqb].
   rewrite ?Source,?Z.add_0_r,?(word_fits (meta+72)) by (unfold word64;lia).
   rewrite ?Count,?W,?A,?B;repeat split;auto.
Qed.

Lemma accepted_index mask o meta out len active j idx s c : args mask meta out len active j s -> (j<active<=8)%nat ->
 fits64 meta 80 -> word64 len -> 0<=idx<len -> read_word (mem s) (index_address meta j)=idx ->
 exists u,run 3 (fetch_at o) (State (Running 18) s c)=Some(State (Running 28) u (Some true),[]) /\
 args mask meta out len active j u /\ regs u 9%nat=idx /\ mem u=mem s.
Proof.
 intros Reg J [L H] Length X Word;destruct Reg as [Ptr [Dst [Len [AX [I Count]]]]].
 assert (Addr:word (meta+Z.of_nat j*8+8)=index_address meta j)
   by (unfold index_address;rewrite word_fits;unfold word64;lia).
 assert (Base:word idx=idx) by (apply word_fits;unfold word64 in *;lia).
 assert (Less:(idx<?len)=true) by (apply Z.ltb_lt;lia).
 eexists;split.
 - apply (checked _ _ _ (proj1(proj2 bytes_bound))).
   cbn [guard follow loc cf cpu_state step option_map eval_condition effective set set_regs with_zf regs put Nat.eqb].
   rewrite Ptr,I,Addr,Word,Base,Len,(word_fits _ Length),Less;reflexivity.
 - unfold args;cbn [guard follow loc cf cpu_state step option_map eval_condition effective set set_regs with_zf regs mem put Nat.eqb].
   rewrite ?Ptr,?I,?Addr,?Word;repeat split;auto.
Qed.

Lemma low_value s r z : regs (low_byte s r z) r mod 256=z mod 256.
Proof.
 unfold low_byte;cbn [set set_regs regs with_words];unfold put;rewrite Nat.eqb_refl.
 pose proof(Z.div_mod (regs s r) 256 ltac:(lia)) as D.
 replace (regs s r-regs s r mod 256+z mod 256) with (z mod 256+(regs s r/256)*256) by lia.
 rewrite Z.mod_add,Z.mod_mod by lia;reflexivity.
Qed.

Lemma written mask flags o meta out len active j idx s c : args mask meta out len active j s -> regs s 9%nat=idx ->
 (j<active<=8)%nat -> fits64 meta 80 -> flags j=mem s (meta+Z.of_nat j) -> fits64 out len -> 0<=idx<len ->
 exists t cf ws,run 7 (fetch_at o) (State (Running 28) s c)=Some(State (Running (next active (S j))) t cf,ws) /\
 args mask meta out len active (S j) t /\ mem t=write_bytes (mem s) (out+idx) 1 (fun _=>verdict flags mask j) /\
 confined (fun x=>x=out+idx) ws.
Proof.
 intros [Ptr [Dst [Len [AX [I Count]]]]] Index J [ML MH] Flag [O U] X.
 set (loaded:=low_byte s 10 (mem s (effective s (Address 7 (Some (8%nat,1)) 0)))).
 set (z:=Z.land (regs loaded 10%nat mod 256) (regs loaded 0%nat mod 256)).
 set (v:=low_byte loaded 10 z).
 assert (Input:effective s (Address 7 (Some (8%nat,1)) 0)=meta+Z.of_nat j).
 { unfold effective;cbn;rewrite Ptr,I,word_fits by (unfold word64;lia);ring. }
 assert (Low:regs v 10%nat mod 256=verdict flags mask j).
 { unfold v;rewrite low_value;unfold z;change (regs loaded 0%nat) with (regs s 0%nat).
   unfold loaded;rewrite low_value,Input,<-Flag,AX;reflexivity. }
 assert (W:word (Z.of_nat j+1)=Z.of_nat(S j)) by (rewrite word_fits;unfold word64;lia).
 assert (Cur:word (Z.of_nat(S j))=Z.of_nat(S j)) by (apply word_fits;unfold word64;lia).
 assert (Limit:word (Z.of_nat active)=Z.of_nat active) by (apply word_fits;unfold word64;lia).
 assert (PC:(if Z.of_nat(S j)<?Z.of_nat active then 18 else 49)=next active (S j)).
 { unfold next;destruct (Z.ltb_spec (Z.of_nat(S j)) (Z.of_nat active)),(Nat.ltb_spec (S j) active);try reflexivity;lia. }
 do 3 eexists;split.
 - apply (checked _ _ _ (proj1(proj2(proj2 bytes_bound)))).
   cbn [publish follow loc cf cpu_state step option_map eval_condition regs set set_regs with_zf flag byte_step with_words put Nat.eqb low_byte].
   rewrite I,W,Cur,Count,Limit,<-PC;reflexivity.
 - unfold args;cbn [publish follow loc cf cpu_state step eval_condition option_map with_zf set set_regs flag regs mem
     with_words byte_step put Nat.eqb].
   split;[repeat split;try assumption;try reflexivity;now rewrite AX|].
   split.
   + change (write_bytes (mem s) (word(regs s 6%nat+regs s 9%nat)) 1 (fun _=>regs v 10%nat mod 256)=
             write_bytes (mem s) (out+idx) 1 (fun _=>verdict flags mask j)).
     rewrite Dst,Index,(word_fits (out+idx)) by (unfold word64;lia);rewrite Low;reflexivity.
   + constructor;[|constructor];intros x Touch;unfold touches,byte_store in Touch.
     change (word(regs s 6%nat+regs s 9%nat)<=x<word(regs s 6%nat+regs s 9%nat)+1) in Touch.
     rewrite Dst,Index,word_fits in Touch by (unfold word64;lia);lia.
Qed.

Definition flags_at m meta n (flags:nat->Z):=forall j,(j<n)%nat -> m(meta+Z.of_nat j)=flags j.
Definition compatible (idx:nat->Z) n (value:nat->Z):=forall i j,(i<n)%nat -> (j<n)%nat -> idx i=idx j -> value i=value j.
Definition published m out (idx:nat->Z) n (value:nat->Z):=forall j,(j<n)%nat -> m(out+idx j)=value j.
Definition targets out (idx:nat->Z) first n x:=exists j,(first<=j<first+n)%nat /\ x=out+idx j.

Lemma loop mask flags o meta out len active idx : (0<active<=8)%nat -> fits64 meta 80 -> word64 len -> fits64 out len ->
 disjoint meta 80 out len -> (forall j,(j<active)%nat -> 0<=idx j<len) ->
 compatible idx active (verdict flags mask) -> forall fuel j s c,(j+fuel=active)%nat -> args mask meta out len active j s -> indices (mem s) meta active idx -> flags_at (mem s) meta active flags ->
 published (mem s) out idx j (verdict flags mask) -> exists t cf ws,run (10*fuel) (fetch_at o) (State (Running (next active j)) s c)=
 Some(State (Running 49) t cf,ws) /\ published (mem t) out idx active (verdict flags mask) /\ confined (targets out idx j fuel) ws.
Proof.
 intros Active Meta Len Out Sep Bounds Compat fuel;induction fuel as [|f IH];intros j s c Left Args Ind Flags Prev.
 - replace j with active in * by lia;unfold next;rewrite Nat.ltb_irrefl;do 3 eexists;split;[reflexivity|split;[exact Prev|constructor]].
 - assert (J:(j<active)%nat) by lia.
   destruct(accepted_index mask o meta out len active j (idx j) s c Args ltac:(lia) Meta Len (Bounds j J) (Ind j J))
     as [u [Check [U [Index M]]]].
   destruct(written mask flags o meta out len active j (idx j) u (Some true) U Index ltac:(lia) Meta ltac:(rewrite M;exact (eq_sym(Flags j J))) Out (Bounds j J))
     as [v [cv [w [Write [V [Flat Safe]]]]]].
   assert (I:indices (mem v) meta active idx).
   { intros i K;rewrite Flat,M,<- (Ind i K);apply preserved_read with (outside:=fun x=>~(out<=x<out+len)).
     - intros x X;apply write_outside;pose proof(Bounds j J);lia.
     - intros k K';change (0<=k<8) in K';unfold index_address,disjoint in *;lia. }
   assert (F:flags_at (mem v) meta active flags).
   { intros i K;rewrite Flat,M,write_outside;[apply Flags,K|pose proof(Bounds j J);unfold disjoint in *;lia]. }
   assert (Z:published (mem v) out idx (S j) (verdict flags mask)).
   { intros i K;rewrite Flat,M;destruct(Z.eq_dec (idx i) (idx j)) as [Eq|Ne].
     - rewrite (Compat i j ltac:(lia) J Eq),Eq;replace (out+idx j) with ((out+idx j)+0) at 2 by ring;apply write_at;lia.
     - rewrite write_outside by lia;apply Prev;destruct(Nat.eq_dec i j);subst;lia. }
   destruct(IH (S j) v cv ltac:(lia) V I F Z) as [t [end_cf [tail [Rest [All W]]]]].
   exists t,end_cf,(w++tail);split;[|split;[exact All|]].
   2:{ apply Forall_app;split.
       - eapply Forall_impl;[|exact Safe];intros a A x X;exists j;split;[lia|exact (A x X)].
       - eapply Forall_impl;[|exact W];intros a A x X;destruct(A x X) as [i [Range E]];exists i;split;[lia|exact E]. }
   unfold next at 1;rewrite (proj2(Nat.ltb_lt _ _) J);replace (10*S f)%nat with (10+10*f)%nat by lia.
   exact (run_append _ 10 _ _ _ (run_append _ 3 _ _ _ Check 7 _ _ Write) _ _ _ Rest).
Qed.
Lemma finish o s c : exists t back,run 2 (fetch_at o) (State (Running 49) s c)=Some(t,[]) /\
 loc t=Returned back /\ regs(cpu_state t) 0%nat=1 /\ mem(cpu_state t)=mem s.
Proof. do 2 eexists;split;[apply (checked _ _ _ (proj2(proj2(proj2 bytes_bound))));reflexivity|repeat split;reflexivity]. Qed.

Theorem returns_exact mask flags o s c meta out len active idx : (0<active<=8)%nat -> fits64 meta 80 ->
 word64 len -> fits64 out len -> disjoint meta 80 out len -> (forall j,(j<active)%nat -> 0<=idx j<len) ->
 regs s 7%nat=meta -> regs s 6%nat=out -> regs s 2%nat=len -> regs s 0%nat=mask ->
 read_word (mem s) (meta+72)=Z.of_nat active -> indices (mem s) meta active idx -> flags_at (mem s) meta active flags ->
 compatible idx active (verdict flags mask) ->
 exists t ws back,run (6+10*active+2) (fetch_at o) (State (Running 0) s c)=Some(t,ws) /\
 loc t=Returned back /\ regs(cpu_state t) 0%nat=1 /\ published (mem(cpu_state t)) out idx active (verdict flags mask) /\
 confined (targets out idx 0 active) ws.
Proof.
 intros N Meta Len Out Sep Bounds DI SI DX AX Count Ind Flags Compat.
 destruct(start mask o s c meta out len active N Meta DI SI DX AX Count) as [u [Head [Args Flat]]].
 destruct(loop mask flags o meta out len active idx N Meta Len Out Sep Bounds Compat active 0 u (Some false) eq_refl
   Args ltac:(now rewrite Flat) ltac:(now rewrite Flat) ltac:(intros i I;lia)) as [v [cf [w [Body [Data Safe]]]]].
 unfold next in Body at 1;rewrite (proj2 (Nat.ltb_lt 0 active) ltac:(lia)) in Body.
 destruct(finish o v cf) as [t [back [End [PC [Status M]]]]].
 exists t,w,back;split.
 - pose proof (run_append _ _ _ _ _ (run_append _ _ _ _ _ Head _ _ _ Body) _ _ _ End) as R;now rewrite app_nil_r in R.
 - split;[exact PC|split;[exact Status|rewrite M;auto]].
Qed.

Theorem returns mask flags o s c meta out len active idx : (0<active<=8)%nat -> fits64 meta 80 ->
 word64 len -> fits64 out len -> disjoint meta 80 out len -> (forall j,(j<active)%nat -> 0<=idx j<len) ->
 regs s 7%nat=meta -> regs s 6%nat=out -> regs s 2%nat=len -> regs s 0%nat=mask ->
 read_word (mem s) (meta+72)=Z.of_nat active -> indices (mem s) meta active idx -> flags_at (mem s) meta active flags ->
 compatible idx active (verdict flags mask) ->
 exists t ws back,run (6+10*active+2) (fetch_at o) (State (Running 0) s c)=Some(t,ws) /\
 loc t=Returned back /\ regs(cpu_state t) 0%nat=1 /\ published (mem(cpu_state t)) out idx active (verdict flags mask) /\
 confined (fun x=>out<=x<out+len) ws.
Proof.
 intros N Fit Len Out Sep Bounds DI SI DX AX Count Ind Flags Compat.
 destruct(returns_exact mask flags o s c meta out len active idx N Fit Len Out Sep Bounds DI SI DX AX Count Ind Flags Compat)
    as [t [ws [back [Run [PC [OK [Values W]]]]]]].
 exists t,ws,back;split;[exact Run|split;[exact PC|split;[exact OK|split;[exact Values|]]]].
 eapply Forall_impl;[|exact W];intros a A x X;destruct(A x X) as [i [I ->]];specialize(Bounds i ltac:(lia));lia.
Qed.

Lemma remaining_shift mask j:0<=mask<256 -> remaining mask j=Z.shiftr mask (Z.of_nat j) /\ 0<=remaining mask j<256.
Proof.
 intro M;induction j as [|j [Eq Bounds]];[split;[symmetry;apply Z.shiftr_0_r|exact M]|].
 cbn [remaining];rewrite !(Z.mod_small (remaining mask j) (2^32)) by lia;split;[|pose proof(Z.div_mod (remaining mask j) 2 ltac:(lia));pose proof(Z.mod_pos_bound (remaining mask j) 2 ltac:(lia));lia].
 rewrite Nat2Z.inj_succ;replace (Z.succ (Z.of_nat j)) with (Z.of_nat j+1) by ring.
 rewrite <-Z.shiftr_shiftr by lia;rewrite <-Eq,Z.shiftr_div_pow2 by lia;reflexivity.
Qed.

Lemma bit_value flags mask j:(flags j=0 \/ flags j=1) -> 0<=mask<256 ->
 verdict flags mask j=Z.b2z((flags j=?1) && Z.testbit mask (Z.of_nat j)).
Proof.
 intros Flag M;destruct(remaining_shift mask j M) as [Eq Bounds];unfold verdict.
 rewrite (Z.mod_small (remaining mask j) 256 Bounds).
 destruct Flag as [Z|One];[rewrite Z;reflexivity|rewrite One;change (1 mod 256) with 1].
 rewrite Z.land_comm;change 1 with (Z.ones 1) at 1;rewrite Z.land_ones by lia.
 change (2^1) with 2.
 rewrite (Z.mod_small (remaining mask j mod 2) 256) by (pose proof(Z.mod_pos_bound (remaining mask j) 2 ltac:(lia));lia).
 rewrite Eq;change (1=?1) with true;rewrite andb_true_l.
 replace (Z.testbit mask (Z.of_nat j)) with (Z.testbit (Z.shiftr mask (Z.of_nat j)) 0) by
   (rewrite Z.shiftr_spec,Z.add_0_l by lia;reflexivity).
 rewrite <-Z.bit0_mod;reflexivity.
Qed.
