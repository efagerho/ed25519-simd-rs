From Coq Require Import List ZArith NArith Strings.Byte Bool Lia.
From Machine Require Import execution.LinkedCalls memory.ByteMemory memory.FlatMemory.
From SHA512 Require Import Spec.
From Ed25519Simd.Sha512Challenge Require Import Output Loader Transpose Lanes.
Import ListNotations.
Local Open Scope nat_scope.

Definition length_at s (m:bytes) j := Z.to_nat (read_word m (regs s 8%nat + 8*Z.of_nat j)%Z).
Definition pointer_at s (m:bytes) j := read_word m (regs s 1%nat + 8*Z.of_nat j)%Z.
Definition read_byte (m:bytes) a := low_byte (Z.to_N (m a)).
Definition byte_offset (p:Z) k := (p+Z.of_nat k)%Z.
Definition prefix_byte s m j k :=
  if k <? 32 then read_byte m (byte_offset (regs s 6%nat + 32*Z.of_nat j) k)
  else read_byte m (byte_offset (regs s 2%nat + 32*Z.of_nat j) (k-32)).
Definition short_rows s m off := existsb (fun j=>length_at s m j <? off+64) (seq 0 8).
(* The first bit enables a memory read. The second enables the subsequent
   merge from the register containing 0x80. *)
Definition row_masks s m off j k :=
  if short_rows s m off then
    let len:=length_at s m j in
    if len <? off then (false,false) else
    let count:=len-off in if 64 <=? count then (true,false) else
    let marker:=N.shiftl 1 (N.of_nat (count mod 64)) in
    (N.testbit (N.pred marker) (N.of_nat k), N.testbit marker (N.of_nat k))
  else (true,false).
Definition reads_message s m off j k := fst (row_masks s m off j k).
Definition message_row s m off j k :=
  let '(load,mark):=row_masks s m off j k in
  let data:=if load then read_byte m (byte_offset (pointer_at s m j) (off+k)) else x00 in
  if mark then x80 else data.
Definition row_input s m t cursor first r k :=
  let j:=r-8 in
  if (t =? 0) && (first =? 0) then prefix_byte s m j k
  else message_row s m (if first =? 0 then cursor-64 else cursor) j k.
Definition native_column s m t cursor lane i :=
  let first:=if i <? 64 then 0 else 8 in
  match route first (first+(i mod 64)/8) (8*lane+(7-i mod 8)) with
  | Input r k=>row_input s m t cursor first r k
  | Literal v=>low_byte (N.of_nat v) | Unknown=>x00 end.
Definition native_block s m t cursor lane finished tail :=
  map (fun i=>if finished && (112 <=? i) then nth (i-112) tail x00
               else native_column s m t cursor lane i) (seq 0 128).

Lemma fast_row s m off j : j<8 -> short_rows s m off=false -> off+64<=length_at s m j.
Proof.
 intros J F. destruct (Nat.lt_ge_cases (length_at s m j) (off+64));auto.
 assert (T:short_rows s m off=true) by
   (apply existsb_exists; exists j; split; [apply in_seq|apply Nat.ltb_lt];lia). congruence.
Qed.
Lemma masked_reads s m off j k : j<8 -> k<64 ->
  (reads_message s m off j k=true <-> off+k<length_at s m j).
Proof.
 intros J K. unfold reads_message,row_masks. destruct (short_rows s m off) eqn:F.
 - destruct (Nat.ltb_spec (length_at s m j) off).
   + split; [discriminate|lia].
   + destruct (Nat.leb_spec 64 (length_at s m j-off)).
     * split; [lia|auto].
     * cbn [fst]. rewrite Nat.mod_small, N.shiftl_1_l, <- N.ones_equiv by lia.
       destruct (Nat.ltb_spec k (length_at s m j-off)).
       -- rewrite N.ones_spec_low by lia. split; auto; lia.
       -- rewrite N.ones_spec_high by lia. split; [discriminate|lia].
 - pose proof (fast_row _ _ _ _ J F). split; auto; lia.
Qed.

Definition msg_bytes s j := input_bytes (mem s) (pointer_at s (mem s) j) (length_at s (mem s) j).
Definition input_agreement s m := forall j,j<8 ->
 length_at s m j=length_at s (mem s) j /\ pointer_at s m j=pointer_at s (mem s) j /\
 (forall addr, In addr [(regs s 6%nat + 32*Z.of_nat j)%Z;(regs s 2%nat + 32*Z.of_nat j)%Z] ->
   forall k,k<32 -> m (byte_offset addr k)=mem s (byte_offset addr k)) /\
 (forall k,k<length_at s (mem s) j ->
   m (byte_offset (pointer_at s (mem s) j) k)=mem s (byte_offset (pointer_at s (mem s) j) k)).
Local Lemma input_length m a n : length (input_bytes m a n)=n.
Proof. unfold input_bytes. now rewrite map_length,seq_length. Qed.
Local Lemma input_nth m a n i : i<n -> nth i (input_bytes m a n) x00=read_byte m (byte_offset a i).
Proof.
  intro I. unfold input_bytes. change (nth i (map (fun k=>read_byte m (byte_offset a k)) (seq 0 n)) x00 =
    read_byte m (byte_offset a i)).
  exact (nth_seq_map (fun k=>read_byte m (byte_offset a k)) n i x00 I).
Qed.
Local Lemma message_at s j off i :
 64<=off -> marked (challenge_input s j) (off+i) = marked (msg_bytes s j) (off-64+i).
Proof.
 intro O. unfold marked. rewrite challenge_size. unfold msg_bytes. rewrite input_length.
 change (Z.to_nat (message_length s j)) with (length_at s (mem s) j).
 destruct (Nat.ltb_spec (off+i) (64+length_at s (mem s) j)),
          (Nat.ltb_spec (off-64+i) (length_at s (mem s) j));try lia.
 - unfold challenge_input. rewrite !app_nth2, !input_length by (rewrite ?input_length;lia).
   f_equal; lia.
 - destruct (Nat.eqb_spec (off+i) (64+length_at s (mem s) j)),
          (Nat.eqb_spec (off-64+i) (length_at s (mem s) j));auto;lia.
Qed.
Local Lemma prefix_correct s m j k : input_agreement s m -> j<8 -> k<64 ->
 prefix_byte s m j k = marked (challenge_input s j) k.
Proof.
 intros A J K. destruct (A j J) as [_ [_ [P _]]].
 unfold prefix_byte,marked. rewrite challenge_size. rewrite (proj2 (Nat.ltb_lt k (64+Z.to_nat (message_length s j))) ltac:(lia)).
 unfold challenge_input. destruct (Nat.ltb_spec k 32).
 - rewrite app_nth1,input_nth by (rewrite ?input_length;lia).
   unfold read_byte;rewrite P by (simpl;auto);auto.
 - rewrite app_nth2,input_length,app_nth1,input_nth by (rewrite ?input_length;lia).
   unfold read_byte;rewrite P by (simpl;intuition lia);auto.
Qed.
Local Lemma row_correct s m off j k : input_agreement s m -> j<8 -> k<64 ->
 message_row s m off j k = marked (msg_bytes s j) (off+k).
Proof.
 intros A J K. destruct (A j J) as [Len [Ptr [_ M]]].
 assert (N : length (msg_bytes s j)=length_at s m j)
   by (unfold msg_bytes;rewrite input_length,Len;reflexivity).
 assert (V:off+k<length_at s m j ->
    read_byte m (byte_offset (pointer_at s m j) (off+k))=nth (off+k) (msg_bytes s j) x00).
 { intro I. unfold msg_bytes. rewrite input_nth by lia. unfold read_byte. now rewrite Ptr,M by lia. }
 unfold message_row,row_masks.
 destruct (short_rows s m off) eqn:F.
 - rewrite <- row_byte_correct by auto. unfold row_byte. rewrite N.
   destruct (Nat.ltb_spec (length_at s m j) off);auto.
   destruct (Nat.leb_spec 64 (length_at s m j-off));[apply V;lia|].
   unfold partial_byte.
   set (r:=length_at s m j-off). rewrite Nat.mod_small,N.shiftl_1_l,<-N.ones_equiv by (unfold r;lia).
   destruct (N.testbit (2 ^ N.of_nat r) (N.of_nat k));auto.
   destruct (Nat.ltb_spec k r); [rewrite N.ones_spec_low by lia;apply V;unfold r in *;lia|
     now rewrite N.ones_spec_high by lia].
 - pose proof (fast_row _ _ _ _ J F). unfold marked. rewrite N.
   rewrite (proj2 (Nat.ltb_lt (off+k) (length_at s m j)) ltac:(lia)). apply V;lia.
Qed.

Lemma native_block_correct s m t j f tail : input_agreement s m -> j<8 ->
 native_block s m t (128*t) j f tail = gather_from (challenge_input s) t j f tail.
Proof.
 intros A J. unfold native_block,gather_from. apply map_ext_in. intros i I. apply in_seq in I.
 destruct (_ && _);auto. unfold native_column,column_byte.
 set (first:=if i <? 64 then 0 else 8).
 assert (F:first=0 \/ first=8) by (unfold first;destruct (i <? 64);auto).
 assert (V:i mod 64<64) by (apply Nat.mod_upper_bound;lia).
 assert (B:i mod 8<8) by (apply Nat.mod_upper_bound;lia).
 assert (Q:(i mod 64)/8<8) by (apply Nat.div_lt_upper_bound;lia).
 rewrite transpose_bytes by (try assumption;lia).
 unfold row_input. replace (8+j-8) with j by lia.
 set (k:=8*(i mod 64/8)+7-(7-i mod 8)).
 assert (K:k<64) by (unfold k;lia).
 rewrite load_correct by (rewrite challenge_size;lia).
 destruct (Nat.eqb_spec t 0), (Nat.eqb_spec first 0); cbn [andb].
 { subst t first. rewrite prefix_correct by auto. f_equal;lia. }
 all: rewrite row_correct by auto; rewrite message_at by lia; f_equal;lia.
Qed.
