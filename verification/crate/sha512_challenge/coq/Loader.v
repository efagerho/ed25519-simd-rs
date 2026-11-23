From Coq Require Import List Bool PeanoNat NArith Strings.Byte Lia.
From SHA512 Require Import Spec Facts.
Import ListNotations.
Local Open Scope nat_scope.

(* The subtract/borrow branch skips the pointer load for already exhausted
   rows. In the partial row only bytes below the remaining count are read. *)
Definition partial_byte (m:list byte) off i remaining :=
  let marker := N.shiftl 1 (N.of_nat (remaining mod 64)) in
  let loaded := if N.testbit (N.pred marker) (N.of_nat i) then nth (off+i) m x00 else x00 in
  if N.testbit marker (N.of_nat i) then x80 else loaded.
Lemma partial_correct m off i r : r < 64 ->
  partial_byte m off i r =
  if i =? r then x80 else if i <? r then nth (off+i) m x00 else x00.
Proof.
  intro R. unfold partial_byte. rewrite Nat.mod_small, N.shiftl_1_l, N.pow2_bits_eqb,
    <- N.ones_equiv by auto.
  destruct (Nat.eqb_spec i r), (N.eqb_spec (N.of_nat r) (N.of_nat i)); try lia; auto.
  destruct (Nat.ltb_spec i r); [rewrite N.ones_spec_low|rewrite N.ones_spec_high]; auto; lia.
Qed.
Definition row_byte (m:list byte) off i :=
  if length m <? off then x00 else
  let remaining := length m - off in
  if 64 <=? remaining then nth (off+i) m x00 else
  partial_byte m off i remaining.
Definition marked (m:list byte) i :=
  if i <? length m then nth i m x00 else if i =? length m then x80 else x00.
Lemma row_byte_correct m off i : i < 64 -> row_byte m off i = marked m (off+i).
Proof.
  intro I. unfold row_byte, marked.
  repeat match goal with
  | |- context [if ?x <? ?y then _ else _] => destruct (Nat.ltb_spec x y)
  | |- context [if ?x <=? ?y then _ else _] => destruct (Nat.leb_spec x y)
  | |- context [if ?x =? ?y then _ else _] => destruct (Nat.eqb_spec x y)
  end; try reflexivity; try lia; rewrite partial_correct by lia;
    destruct (Nat.eqb_spec i (length m-off)), (Nat.ltb_spec i (length m-off)); auto; lia.
Qed.

Lemma nth_after_skip {A} n (xs:list A) i d :
  nth i (skipn n xs) d = nth (n+i) xs d.
Proof. revert xs. induction n;intros [|x xs];cbn;auto;now destruct i. Qed.
Lemma nth_before_cut {A} n (xs:list A) i d : i<n ->
  nth i (firstn n xs) d = nth i xs d.
Proof. revert xs i. induction n;intros [|x xs] [|i] I;cbn;auto;try lia. apply IHn;lia. Qed.

Definition load_byte (msg:list byte) pos :=
  if pos <? 64 then nth pos msg x00 else
  let m := skipn 64 msg in
  row_byte m (64*((pos-64)/64)) ((pos-64) mod 64).
Lemma load_correct msg pos : 64 <= length msg -> load_byte msg pos = marked msg pos.
Proof.
  intro L. unfold load_byte. destruct (Nat.ltb_spec pos 64).
  - unfold marked. now rewrite (proj2 (Nat.ltb_lt pos (length msg)) ltac:(lia)).
  - rewrite row_byte_correct by (apply Nat.mod_upper_bound; lia).
    rewrite <- Nat.div_mod by lia. unfold marked. rewrite skipn_length.
    assert (E : (pos-64 <? length msg-64) = (pos <? length msg))
      by (destruct (Nat.ltb_spec pos (length msg)), (Nat.ltb_spec (pos-64) (length msg-64)); auto; lia).
    rewrite E. destruct (pos <? length msg).
    + rewrite nth_after_skip. f_equal; lia.
    + destruct (Nat.eqb_spec pos (length msg)), (Nat.eqb_spec (pos-64) (length msg-64)); auto; lia.
Qed.

Definition last_block (msg:list byte) := (length msg - 64 + 80)/128.
Definition trailer (msg:list byte) :=
  let bytes := N.of_nat (length msg) in
  big_endian 8 (N.shiftr bytes 61) ++ big_endian 8 (word (N.shiftl bytes 3)).
Lemma encode_byte n x i : i<n ->
 nth i (big_endian n x) x00 = low_byte (x / 256 ^ N.of_nat (n-1-i)).
Proof.
  revert x i. induction n as [|n IH]; intros x i I; [lia|].
  cbn [big_endian]. destruct (Nat.eq_dec i n) as [->|D].
  - rewrite app_nth2, big_endian_length by (rewrite ?big_endian_length; lia).
    rewrite Nat.sub_diag. replace (S n - 1 - n) with 0 by lia. cbn. now rewrite N.div_1_r.
  - rewrite app_nth1 by (rewrite big_endian_length; lia). rewrite IH by lia.
    f_equal. rewrite N.Div0.div_div.
    replace (S n - 1 - i) with (S (n-1-i)) by lia.
    now rewrite Nat2N.inj_succ, N.pow_succ_r'.
Qed.
Local Lemma encode_mod n x : big_endian n (x mod (256^N.of_nat n)) = big_endian n x.
Proof.
  apply nth_ext with (d:=x00) (d':=x00); rewrite !big_endian_length; auto.
  intros i I. rewrite !encode_byte by exact I. unfold low_byte.
  replace (256^N.of_nat n)%N with
    ((256^N.of_nat (n-1-i)) * (256*256^N.of_nat i))%N.
  2:{ rewrite <- N.pow_succ_r', <- N.pow_add_r, <- Nat2N.inj_succ, <- Nat2N.inj_add.
      f_equal. lia. }
  set (p:= (256^N.of_nat (n-1-i))%N).
  assert (P : p <> 0%N) by (apply N.pow_nonzero; discriminate).
  rewrite N.Div0.mod_mul_r, (N.mul_comm p), N.div_add by auto.
  rewrite N.div_small by (apply N.mod_lt; auto). rewrite N.add_0_l.
  rewrite N.Div0.mod_mul_r, (N.mul_comm 256), N.mod_add, N.mod_mod by discriminate.
  reflexivity.
Qed.

Lemma trailer_correct msg : trailer msg = big_endian 16 (bit_length msg).
Proof.
  unfold trailer, bit_length, word. set (n:=N.of_nat (length msg)).
  rewrite N.shiftr_div_pow2, N.shiftl_mul_pow2.
  change (n / 2 ^ 61)%N with (n / 2305843009213693952)%N.
  replace (n*2^3)%N with (8*n)%N by apply N.mul_comm.
  change (2^64)%N with (256^N.of_nat 8)%N. rewrite encode_mod.
  apply nth_ext with (d:=x00) (d':=x00).
  - rewrite app_length, !big_endian_length. reflexivity.
  - intros i I. rewrite app_length, !big_endian_length in I.
    destruct (Nat.lt_ge_cases i 8) as [L|L].
    + rewrite app_nth1 by (rewrite big_endian_length; lia). rewrite !encode_byte by lia.
      f_equal. replace (16-1-i) with (8+(8-1-i)) by lia.
      rewrite Nat2N.inj_add, N.pow_add_r, <- N.div_div by (apply N.pow_nonzero; discriminate).
      change (256^N.of_nat 8)%N with (8*2305843009213693952)%N.
      now rewrite N.div_mul_cancel_l by discriminate.
    + rewrite app_nth2, big_endian_length by (rewrite ?big_endian_length; lia).
      rewrite !encode_byte by lia. replace (8-1-(i-8)) with (16-1-i) by lia. reflexivity.
Qed.

Definition octet msg block i :=
  if (block =? last_block msg) && (112 <=? i) then nth (i-112) (trailer msg) x00
  else load_byte msg (128*block+i).
Definition load_block msg block := map (octet msg block) (seq 0 128).

Lemma last_index msg : 64 <= length msg -> last_block msg = (length msg + 16)/128.
Proof. intro L. unfold last_block. f_equal; lia. Qed.
Lemma padded_size msg : 64 <= length msg -> length (pad msg) = 128*S(last_block msg).
Proof. intro L. rewrite padded_length, last_index by auto. reflexivity. Qed.
Local Lemma marker_bytes msg g :
  nth g (msg ++ [x80] ++ repeat x00 (zero_count (length msg))) x00 = marked msg g.
Proof.
  unfold marked. destruct (Nat.ltb_spec g (length msg)).
  - now rewrite app_nth1 by lia.
  - rewrite app_nth2 by lia. destruct (Nat.eqb_spec g (length msg)) as [->|D].
    + now rewrite Nat.sub_diag.
    + destruct (g-length msg) eqn:G; [lia|]. cbn. apply nth_repeat.
Qed.

Lemma octet_correct msg t i : 64 <= length msg -> t <= last_block msg -> i<128 ->
  octet msg t i = nth (128*t+i) (pad msg) x00.
Proof.
  intros L T I. unfold octet. rewrite trailer_correct.
  pose proof (padded_size msg L) as P. unfold pad in *.
  set (head:=msg ++ [x80] ++ repeat x00 (zero_count (length msg))).
  replace (msg ++ [x80] ++ repeat x00 (zero_count (length msg)) ++ big_endian 16 (bit_length msg))
    with (head ++ big_endian 16 (bit_length msg)) in * by (unfold head; now rewrite <- !app_assoc).
  rewrite app_length, big_endian_length in P.
  destruct (Nat.eqb_spec t (last_block msg)), (Nat.leb_spec 112 i); cbn [andb].
  { rewrite app_nth2 by lia. f_equal; lia. }
  all: rewrite app_nth1 by lia; rewrite load_correct by assumption; symmetry; apply marker_bytes.
Qed.
