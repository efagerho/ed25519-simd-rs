From Coq Require Import List ZArith NArith Strings.Byte Bool Lia.
From Machine Require Import execution.LinkedCalls execution.WordSemantics execution.WordBounds
 memory.FlatMemory memory.ByteMemory memory.MemoryGeometry memory.Alignment.
From SHA512 Require Import Spec Facts.
From Ed25519Simd.Sha512Challenge Require Import Compression Block Loader Lanes Frame Output Image Execution Rows.
Import ListNotations.
Local Open Scope Z_scope.

Definition address s j i := cell (dst s) (i/8) j + Z.of_nat (i mod 8).
Definition byte_at bs i := Z.of_N (Byte.to_N (nth i bs x00)).
Definition represents_output s m (out:nat->list byte) :=
  forall j i, (j<8)%nat -> (i<64)%nat -> (i<length (out j))%nat ->
    m (address s j i) = byte_at (out j) i.
Definition temporary s x := frame s-8 <= x < frame s+512.
Definition destination s x := dst s <= x < dst s+512.
Definition keeps s m := byte_memory m /\
  preserved (fun x=>~temporary s x /\ ~destination s x) (init_frame s) m.
Definition bounded hs := forall j r, (j<8)%nat -> (r<8)%nat -> word64 (Z.of_N (nth r (spill (hs j)) 0%N)).
Lemma bounded_feed s v : forall r, (r<8)%nat -> word64 (Z.of_N (nth r (spill (feed s v)) 0%N)).
Proof.
  assert (B : forall x y, word64 (Z.of_N (add64 x y))).
  { intros x y. unfold add64, Spec.word, word64. split;[apply N2Z.is_nonneg|].
    change (Z.of_N ((x+y) mod 2^64) < Z.of_N (2^64)). apply (proj1 (N2Z.inj_lt _ _)), N.mod_lt;discriminate. }
  intro r. do 8 (destruct r as [|r]; [intros _;apply B|]). lia.
Qed.
Local Lemma byte_bound bs i : 0<=byte_at bs i<256.
Proof. unfold byte_at. pose proof (Byte.to_N_bounded (nth i bs x00)). lia. Qed.
Local Lemma out_range s j i : (j<8)%nat -> (i<64)%nat -> destination s (address s j i).
Proof. intros J I. assert (i/8<8)%nat by (apply Nat.div_lt_upper_bound;lia). unfold destination,address,cell. pose proof (Nat.mod_upper_bound i 8 ltac:(lia)); lia. Qed.
Local Lemma full_store s m t hs j i : (j<8)%nat -> (i<64)%nat ->
 stores s m t hs (address s j i) =
 if finish_mask s m t j then byte_at (emit (hs j)) i else m (address s j i).
Proof.
  intros J I. pose proof (out_range s j i J I) as R. unfold destination in R. unfold stores.
  rewrite (proj2 (Z.leb_le 0 (address s j i-dst s)) ltac:(lia)), (proj2 (Z.ltb_lt (address s j i-dst s) 512) ltac:(lia)). cbn [andb].
  replace (address s j i - dst s) with (64*Z.of_nat (i/8)+8*Z.of_nat j+Z.of_nat (i mod 8))
    by (unfold address,cell;ring).
  pose proof (Nat.mod_upper_bound i 8 ltac:(lia)).
  destruct (indices (i/8) j (Z.of_nat (i mod 8)) J ltac:(lia)) as [A [B C]].
  rewrite A,B,C,Nat2Z.id. replace (Z.to_nat (8*Z.of_nat (i/8)+Z.of_nat (i mod 8))) with i
    by (pose proof (Nat.div_mod i 8 ltac:(lia));lia).
  reflexivity.
Qed.
Local Lemma store_other s m t hs x : ~destination s x -> stores s m t hs x=m x.
Proof. intro X. unfold stores,destination in *. destruct (_ && _ && _)%bool eqn:B; auto.
  rewrite !andb_true_iff in B; destruct B as [[L U] _]. apply Z.leb_le in L; apply Z.ltb_lt in U; lia. Qed.

Section Call.
Variables (s:cpu) (pc size ro:Z).
Hypotheses (P:placement s pc size ro) (W:well_formed s).
Local Lemma stack_below : frame s+704 <= sp s-8.
Proof. unfold frame. pose proof (Z.mod_pos_bound (sp s-8) 64 ltac:(lia));lia. Qed.
Local Lemma apart x : frame s-8 <= x < sp s+8 -> ~destination s x.
Proof. destruct (out_fits _ _ _ _ P) as [_ D]. unfold disjoint, destination in *;lia. Qed.
Local Lemma lengths_ok : bounded_lengths s.
Proof. intros j J; apply (slices_fit _ _ _ _ P j J). Qed.
Local Lemma slot_value m r j : keeps s m -> (r<3)%nat -> (j<8)%nat ->
 length_slot s m r j = length_value s r j.
Proof.
  intros [_ K] R J. unfold length_slot, read_word.
  rewrite (preserved_read 8 _ _ _ _ K).
  - apply matrix_word; [assumption|lia|]. apply (length_words _ _ lengths_ok J).
  - intros k B. unfold temporary,cell. split;[lia|apply apart; pose proof stack_below;lia].
Qed.
Local Lemma last_value m j : keeps s m -> (j<8)%nat ->
 last s m j=last_block (challenge_input s j).
Proof. intros K J. unfold last. rewrite slot_value by auto; try lia.
  now rewrite (proj1 (proj2 (length_words _ _ lengths_ok J))), Nat2Z.id.
Qed.
Local Lemma continues_value m t : keeps s m -> continuing s m t=more (challenge_input s) t.
Proof. intro K. unfold continuing,more. apply eq_true_iff_eq. rewrite !existsb_exists. split; intros [j [J T]];
    exists j; split; auto; apply in_seq in J.
  - now rewrite last_value in T by (auto;lia).
  - now rewrite last_value by (auto;lia).
Qed.
Local Lemma call_ok m ip : word64 ip ->
 call_rows s m ip=Some (store_word m (frame s-8) ip).
Proof. intro H. unfold call_rows,store_word. now rewrite write_read_word, Z.eqb_refl. Qed.

Local Definition temps_only before after := byte_memory after /\
  preserved (fun x=>~temporary s x) before after.
Local Lemma written_temp m base n payload : byte_memory m ->
 frame s-8<=base -> base+n<=frame s+512 ->
 (forall k,0<=k<n -> 0<=payload k<256) ->
 temps_only m (write_bytes m base n payload).
Proof. intros M L U B. split;[now apply write_bytes_well_formed|].
 intros x X. apply write_outside. unfold temporary in X;lia. Qed.
Local Lemma temps_keep m m' : keeps s m -> temps_only m m' -> keeps s m'.
Proof. intros [_ H] [B T];split;auto. intros x [A D];rewrite T by auto;apply H;auto. Qed.
Local Lemma temps_output m m' out : represents_output s m out -> temps_only m m' ->
 represents_output s m' out.
Proof. intros O [_ T] j i J I B. rewrite T; [auto|].
 intro A. apply (apart (address s j i)); [unfold temporary in A;pose proof stack_below;lia|now apply out_range].
Qed.
Local Lemma pushed m ip : byte_memory m -> temps_only m (store_word m (frame s-8) ip).
Proof. intro M. apply written_temp;auto;try lia;intros;apply word_byte_bound. Qed.
Local Lemma spilled m hs : byte_memory m -> temps_only m (spill_frame m s hs).
Proof. intro M. apply written_temp;auto;try lia;intros;apply word_byte_bound. Qed.
Local Lemma reload_ok m hs j : bounded hs -> (j<8)%nat ->
 reload s (spill_frame m s hs) j=hs j.
Proof. intros B J. unfold reload,get_state,spill_frame.
  rewrite !matrix_word by (try lia;apply B;lia). rewrite !N2Z.id.
  destruct (hs j);reflexivity.
Qed.
Local Lemma init_preserves x : ~(frame s+512<=x<frame s+704) -> ~(sp s-8<=x<sp s) ->
 mem s x=init_frame s x.
Proof. intros H1 H2. unfold init_frame,matrix,store_word. rewrite !write_outside by lia. reflexivity. Qed.
Lemma outside m x : keeps s m -> ~writable s x -> m x = mem s x.
Proof.
 intros [_ K] X. unfold writable in X. rewrite K.
 - symmetry. apply init_preserves;pose proof stack_below;lia.
 - unfold temporary,destination. pose proof stack_below; lia.
Qed.
Local Lemma input_stable m : keeps s m -> input_agreement s m.
Proof.
 intro K. assert (S : forall base n, source s base n -> forall x,base<=x<base+n -> m x=mem s x).
 { intros base n [_ [Z|[D F]]] x R;[lia|]. apply outside; [exact K|].
   unfold disjoint in *. unfold writable;lia. }
 destruct (tables_fit _ _ _ _ P) as [R [A [Ptrs Lens]]].
 intro j; intro J.
 assert (T : forall a,source s a 64 -> read_word m (a+8*Z.of_nat j)=read_word (mem s) (a+8*Z.of_nat j)).
 { intros a H. apply (preserved_read 8 _ _ _ _ (S a 64 H)). intros k B;lia. }
 unfold length_at,Rows.pointer_at. rewrite (T _ Lens), (T _ Ptrs).
 split;[reflexivity|]. split;[reflexivity|]. split.
 - intros addr [<-|[<-|[]]] k B;unfold byte_offset; [apply (S _ _ R)|apply (S _ _ A)];lia.
 - intros k B. destruct (slices_fit _ _ _ _ P j J) as [Len Src]. apply (S _ _ Src).
   unfold byte_offset,message_length in *;lia.
Qed.
Local Lemma actual_step m t hs j : bounded hs -> keeps s (spill_frame m s hs) -> (j<8)%nat ->
 hash_step constants s (spill_frame m s hs) t (128*t)%nat hs j = transition (challenge_input s) t hs j.
Proof.
 intros B K J. unfold hash_step, transition, block_step, gather, finish_mask.
 rewrite native_block_correct by auto using input_stable. rewrite reload_ok, last_value, !slot_value by (auto;lia).
 now rewrite (proj2 (proj2 (length_words _ _ lengths_ok J))).
Qed.
Local Lemma store_keeps m t hs : keeps s m -> keeps s (stores s m t hs).
Proof. intros [B F]. split.
 - intro x;unfold stores; destruct (_ && _ && _)%bool;[apply byte_bound|apply B].
 - intros x X. rewrite store_other by tauto. apply F,X.
Qed.

Local Opaque run_lanes.
Local Lemma replay fuel upper lower t hs ls m old out :
 word64 upper -> word64 lower ->
 bounded hs -> (forall j,(j<8)%nat -> hs j=ls j) ->
 keeps s m -> represents_output s m old ->
 loop fuel (challenge_input s) t ls old=Some out ->
 exists final, blocks fuel constants s upper lower 64 t (128*t)%nat hs m=Some final /\
   keeps s final /\ represents_output s final out.
Proof.
 revert t hs ls m old. induction fuel as [|n IH]; intros t hs ls m old U L B Eq K O Run;
 [discriminate|]. cbn [blocks]. rewrite call_ok by auto.
 set (back:=store_word m (frame s-8) upper).
 set (saved:=spill_frame back s hs). set (work:=hash_step constants s saved t (128*t)%nat hs).
 set (updated:=stores s saved t work).
 pose proof (pushed m upper (proj1 K)) as Push. fold back in Push.
 pose proof (spilled back hs (proj1 Push)) as Spill. fold saved in Spill.
 pose proof (temps_keep _ _ (temps_keep _ _ K Push) Spill) as KS.
 pose proof (temps_output _ _ _ (temps_output _ _ _ O Push) Spill) as OS.
 assert (Next : forall j,(j<8)%nat -> work j=transition (challenge_input s) t ls j).
 { intros j J. unfold work, saved. rewrite actual_step by auto.
   unfold transition. now rewrite Eq by auto. }
 assert (BN:bounded work).
 { intros j r J R. unfold work,hash_step. apply bounded_feed,R. }
 pose proof (store_keeps saved t work KS) as KU. fold updated in KU.
 assert (OU:represents_output s updated
    (publish (challenge_input s) t (transition (challenge_input s) t ls) old)).
 { intros j i J I H. unfold updated. rewrite full_store by auto.
   unfold finish_mask,publish in *. rewrite last_value by auto.
   destruct (Nat.eqb t (last_block (challenge_input s j))); [now rewrite Next|now apply OS]. }
 rewrite continues_value by auto. cbn [loop] in Run.
 destruct (more (challenge_input s) t).
 - replace (128*t+64+64)%nat with (128*S t)%nat by lia. rewrite call_ok by auto. pose proof (pushed updated lower (proj1 KU)) as Again.
   apply (IH (S t) work (transition (challenge_input s) t ls) _
      (publish (challenge_input s) t (transition (challenge_input s) t ls) old));
     auto; [eapply temps_keep|eapply temps_output]; eassumption.
 - injection Run as <-. exists updated; auto.
Qed.

Lemma enter_frame : enter s 704 = init_frame s.
Proof.
 unfold enter,push,push_words,init_frame. cbn [with_words mem regs Instructions.put Nat.eqb].
 pose proof (stack_fits _ _ _ _ P) as [Lo Hi]. pose proof stack_below as B.
 fold (sp s). rewrite (word_fits (sp s-8)) by (unfold word64;lia).
 rewrite and_rsp_64. fold (frame s). now rewrite (word_fits (frame s)) by (unfold word64;lia).
Qed.
Local Lemma init_keeps : keeps s (init_frame s).
Proof.
 split;[|intros x X; reflexivity]. unfold init_frame,matrix,store_word.
 apply write_bytes_well_formed;[apply write_bytes_well_formed;[apply W|]|];intros;apply word_byte_bound.
Qed.
Lemma saved_bp m : keeps s m -> read_word m (sp s-8) = regs s 5%nat.
Proof.
 intros [_ K]. unfold read_word. rewrite (preserved_read 8 _ _ _ _ K).
 - unfold init_frame,matrix. apply read_word_exact; [apply W|]. intros k B.
   rewrite write_outside by (pose proof stack_below;lia). apply write_at,B.
 - intros k B. split;[unfold temporary;pose proof stack_below;lia|apply apart;pose proof stack_below;lia].
Qed.
Lemma caller_pc m : keeps s m -> read_word m (sp s) = read_word (mem s) (sp s).
Proof.
 intro K. apply (preserved_read 8 _ _ _ _ (fun x=>outside m x K)).
 intros k B. unfold writable. intros [A|D]; [lia|apply (apart (sp s+k)); [pose proof stack_below;lia|exact D]].
Qed.

Lemma returning_digest upper lower : word64 upper -> word64 lower ->
 exists m, blocks (S (maximum (challenge_input s))) constants s upper lower 64 0 0
   (fun _=>Spec.initial) (init_frame s)=Some m /\
   keeps s m /\ challenge_digests s m.
Proof.
 intros U L. destruct (lanes_correct (challenge_input s)) as [out [R D]];
 [intros j J; rewrite challenge_size; lia|].
 destruct (replay (S (maximum (challenge_input s))) upper lower 0 (fun _=>Spec.initial) (fun _=>Spec.initial)
   (init_frame s) (fun _=>[]) out U L) as [m [Run [K O]]].
 - intros j r J Rr. do 8 (destruct r as [|r]; [vm_compute; split; congruence|]);lia.
 - reflexivity.
 - apply init_keeps.
 - intros j i J I B. cbn in B;lia.
 - exact R.
 - exists m;split;auto. split;auto. intros j J. rewrite <- D by auto.
   apply nth_ext with (d:=0) (d':=0).
   + rewrite !map_length,seq_length,D,sha512_length by auto. reflexivity.
   + intros i I. rewrite map_length, seq_length in I.
     assert (Size:length (out j)=64%nat) by (rewrite D,sha512_length by auto;reflexivity).
     rewrite nth_indep with (d':=m (address s j 0)) by (rewrite map_length,seq_length;lia).
     change (nth i (map (fun k=>m (address s j k)) (seq 0 64)) (m (address s j 0)) =
       nth i (map (fun b=>Z.of_N (Byte.to_N b)) (out j)) 0).
     rewrite (map_nth (fun k=>m (address s j k)) _ 0%nat i), seq_nth by auto.
     change (m (address s j i) = nth i (map (fun b=>Z.of_N (Byte.to_N b)) (out j)) 0).
     rewrite O by lia. symmetry. apply (map_nth (fun b=>Z.of_N (Byte.to_N b)) _ x00).
Qed.
End Call.
