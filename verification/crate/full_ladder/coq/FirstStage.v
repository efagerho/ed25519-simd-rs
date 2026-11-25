From Coq Require Import List ZArith Lia.
From Machine Require Import abi.SysV execution.LinkedCalls memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.FullLadder Require Import LinkedBytes Program Operands Audit.
From Ed25519Simd.FullLadder Require StageEntry.
Import ListNotations. Local Open Scope Z_scope.

(* Staging reads the incoming pointer array, the two digit buffers, and
   table entries selected by those bytes. All lie outside the ladder's
   writable stack. This argument also applies to the later digit pairs. *)
Definition sources_unchanged s u := forall a n,In (a,n) (external_ranges s) ->
 forall x,a<=x<a+n -> mem u x=mem s x.
Definition stage_registers s pad pair u := forall r,In r [1;2;4;6;7;8;9]%nat ->
 regs u r=regs (entry_for pad s pair) r.

Lemma word_unchanged s u a n b : sources_unchanged s u -> In (a,n) (external_ranges s) ->
 a<=b -> b+8<=a+n -> read_word (mem u) b=read_word (mem s) b.
Proof.
 intros H I L R;apply (preserved_read 8 (fun x=>a<=x<a+n));[exact (H a n I)|intros k K;cbn in K;lia].
Qed.

Section Transfer.
Variables (s u:cpu) (pad:Z) (pair:nat).
Hypothesis (G:stage_registers s pad pair u) (Bytes:sources_unchanged s u) (Pair:(pair<32)%nat).
Local Notation model := (entry_for pad s pair).
Local Ltac arg G := rewrite G by (cbv [In];intuition congruence).
Lemma key_pointer j : (j<8)%nat -> SA.key_table u j=SA.key_table model j.
Proof.
 intro J;unfold SA.key_table;arg G;change (regs model 6%nat) with (regs s 6%nat).
 apply (word_unchanged s u (regs s 6%nat) 64);[exact Bytes|left;reflexivity|lia|lia].
Qed.
Lemma digit_value r j p : (r=1%nat \/ r=8%nat) -> (j<8)%nat -> 0<=p<=1 ->
 SA.digit u r j p=SA.digit model r j p.
Proof.
 intros [->| ->] J P;unfold SA.digit,SA.digit_addr;repeat arg G;f_equal.
 all: change (regs model 9%nat) with (Z.of_nat pair).
 - apply (Bytes (regs s 1%nat) 512);[do 2 right;left;reflexivity|].
   change (regs model 1%nat) with (regs s 1%nat);lia.
 - apply (Bytes (regs s 8%nat) 512);[do 3 right;left;reflexivity|].
   change (regs model 8%nat) with (regs s 8%nat);lia.
Qed.
Lemma placement_preserved pc len : SA.placement pc len model -> SA.placement pc len u.
Proof.
 intros [O Al Code Ret SP Ptr Key Base Dg PR Ds];constructor;unfold SA.source in *.
 all: try solve [repeat arg G;assumption].
 - intros j J;arg G;rewrite key_pointer by assumption;apply Key,J.
 - intros r [->| ->];repeat arg G;apply Dg;auto.
 - intros r j p R J P;rewrite digit_value by assumption;apply Ds;assumption.
Qed.
Lemma selected_address k j : (j<8)%nat -> SA.selected u k j=table_address s j (affine k) (weight s j pair k).
Proof.
 intro J;rewrite <-(selected_entry pad s pair k j);destruct k;unfold SA.selected,SA.parity;
 rewrite ?key_pointer,?digit_value by (auto;lia);repeat arg G;reflexivity.
Qed.
Lemma selected_data pc k i j : valid_inputs pc pad s -> (j<8)%nat -> (i<SA.columns k)%nat ->
 read_word (mem u) (SA.selected u k j+8*Z.of_nat i)=table_row s j (affine k) (weight s j pair k) i.
Proof.
 intros V J I;rewrite selected_address by exact J;unfold table_row.
 pose proof(valid_weight pc pad s pair k j V Pair J) as Range.
 assert (K: In (SA.key_table s j,17*160) (external_ranges s)).
 { unfold external_ranges;apply in_or_app;right;apply in_map_iff;exists j;split;[reflexivity|apply in_seq;lia]. }
 destruct k;cbn [affine SA.columns] in *;unfold table_address,legal_index in *.
 all: first [apply (word_unchanged s u (SA.key_table s j) (17*160));[exact Bytes|exact K|unfold SA.key_table;lia|unfold SA.key_table;lia]|
  apply (word_unchanged s u (regs s 2%nat) (273*120));[exact Bytes|right;left;reflexivity|lia|lia]].
Qed.
End Transfer.

Lemma entry_inputs slide s u : placement slide s -> StageEntry.entry_state slide s u ->
 stage_registers s (pad_of s) 31 u /\ sources_unchanged s u.
Proof.
 intros P E;destruct(StageEntry.stage_arguments _ _ _ E) as [SP [DI [SI [DX [CX [R8 [Idx _]]]]]]].
 assert (Align:StageEntry.base (regs s 4%nat)=regs s 4%nat+staging(pad_of s))
  by (unfold StageEntry.base,staging,pad_of;ring).
 split.
 - intros r [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];try assumption;
   unfold entry_for,set,set_regs;cbn [regs Instructions.put Nat.eqb];rewrite <-Align;assumption.
 - intros a n I x R;rewrite (StageEntry.stage_memory _ _ _ E).
   apply (frame _ _ (StageEntry.stage_stack_stores _ _ _ E)).
   destruct (source_regions _ _ P _ _ I) as [_ Apart];unfold FlatMemory.disjoint in Apart;lia.
Qed.

Theorem checked slide s u : placement slide s -> valid_inputs (slide+stage_pc) (pad_of s) s ->
 StageEntry.entry_state slide s u -> let '(ip,v):=S.run (slide+stage_pc) u in first_stage_result slide s u ip v.
Proof.
 intros P V E;destruct(entry_inputs _ _ _ P E) as [G M].
 pose proof(placement_preserved _ _ _ _ G M ltac:(lia) _ _ (proj2 V 31%nat ltac:(lia))) as Layout.
 pose proof(SA.stage_correct _ SO.assembled_stage_round_correct _ _ Layout (StageEntry.stage_words _ _ _ E)) as Post.
 destruct(SA.write_footprint _ SO.assembled_stage_round_correct _ _ Layout) as [Safe Log].
 cbv zeta in Post;destruct(S.run (slide+stage_pc) u) as [ip v] eqn:Run in Post,Log|-*;cbn [snd] in Log.
 destruct Post as [_ [_ [_ [PC [SP [Saved [_ [B Rows]]]]]]]].
 assert (Dst:regs u 7%nat=base_of s) by (apply G;cbv [In];tauto).
 assert (Stack:regs u 4%nat=base_of s-8) by (apply G;cbv [In];tauto).
 constructor.
 - rewrite PC;apply (StageEntry.stage_return_word _ _ _ E).
 - rewrite SP,Stack;ring.
 - exact Saved.
 - exact B.
 - intros x;unfold stage_stores;rewrite replay_app,<-(StageEntry.stage_memory _ _ _ E);apply Log.
 - unfold stage_stores;apply Forall_app;split;[apply (StageEntry.stage_stack_stores _ _ _ E)|].
   eapply Forall_impl;[|exact Safe];intros w W x X;specialize(W x X);unfold SA.destination in W.
   rewrite Dst in W;unfold base_of,staging,pad_of in W;pose proof(Z.mod_pos_bound (regs s 4%nat) 64 ltac:(lia));cbv beta;lia.
 - intros k i j I J;rewrite <-Dst,Rows by assumption.
   eapply selected_data;[exact G|exact M|lia|exact V|exact J|exact I].
Qed.
