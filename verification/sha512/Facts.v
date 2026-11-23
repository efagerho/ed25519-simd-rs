From Coq Require Import List Strings.Byte PeanoNat NArith Lia.
From SHA512 Require Import Spec.
Import ListNotations.

Lemma big_endian_length width x : length (big_endian width x) = width.
Proof.
  revert x. induction width; intro x; cbn [big_endian]; auto.
  rewrite app_length, IHwidth. cbn. lia.
Qed.

Lemma low_byte_value x : Byte.to_N (low_byte x) = (x mod 256)%N.
Proof.
  unfold low_byte. destruct (Byte.of_N (x mod 256)) eqn:E.
  - now apply Byte.to_of_N.
  - apply Byte.of_N_None_iff in E. pose proof (N.mod_lt x 256 ltac:(discriminate)). lia.
Qed.

Lemma read_big_endian_encode width x :
  (x < 256 ^ N.of_nat width)%N -> read_big_endian (big_endian width x) = x.
Proof.
  revert x. induction width as [|n IH]; intros x H.
  - cbn in H. change (0 = x)%N. lia.
  - rewrite Nat2N.inj_succ, N.pow_succ_r' in H.
    cbn [big_endian]. unfold read_big_endian. rewrite fold_left_app.
    fold (read_big_endian (big_endian n (x / 256))).
    rewrite IH by (apply N.div_lt_upper_bound; lia).
    cbn [fold_left]. rewrite low_byte_value. symmetry. apply N.div_mod. discriminate.
Qed.

(* In particular the last two words encode the entire bit count, including
   lengths that overflow a 64-bit bit counter. *)
Lemma length_field_value message :
  (bit_length message < 2^128)%N ->
  read_big_endian (big_endian 16 (bit_length message)) = bit_length message.
Proof. intro H. apply read_big_endian_encode. exact H. Qed.

Lemma padded_length message :
  length (pad message) = 128 * S ((length message + 16) / 128).
Proof.
  unfold pad, zero_count. rewrite !app_length, repeat_length, big_endian_length.
  pose proof (Nat.div_mod (length message + 16) 128 ltac:(lia)).
  pose proof (Nat.mod_upper_bound (length message + 16) 128 ltac:(lia)).
  change (length [x80]) with 1. lia.
Qed.

Lemma chunks_exact {A} n width (xs : list A) :
  length xs = n * width ->
  concat (chunks n width xs) = xs /\ Forall (fun part => length part = width) (chunks n width xs).
Proof.
  revert xs. induction n as [|n IH]; intros xs H.
  - destruct xs; [split; constructor|discriminate].
  - cbn [chunks]. cbn [Nat.mul] in H.
    destruct (IH (skipn width xs)) as [Join Sizes]; [rewrite skipn_length; lia|].
    split.
    + cbn [concat]. rewrite Join. apply firstn_skipn.
    + constructor; auto. rewrite firstn_length. lia.
Qed.

Lemma padded_blocks_exact message :
  let padded := pad message in
  let blocks := chunks (length padded / 128) 128 padded in
  concat blocks = padded /\ Forall (fun block => length block = 128) blocks.
Proof.
  cbv zeta. apply chunks_exact. rewrite padded_length, Nat.mul_comm, Nat.div_mul by lia.
  reflexivity.
Qed.

Lemma chunks_count {A} n width (xs : list A) : length (chunks n width xs) = n.
Proof. revert xs. induction n; intro xs; cbn; auto. Qed.

Lemma compression_round_count block : length (combine constants (schedule block)) = 80.
Proof.
  assert (Expand : forall rounds ws, length (fold_left extend rounds ws) = length ws + length rounds).
  { induction rounds as [|t rest IH]; intro ws; cbn; [lia|].
    rewrite IH. unfold extend. rewrite app_length. cbn. lia. }
  unfold schedule. rewrite combine_length, Expand, map_length, chunks_count, seq_length.
  reflexivity.
Qed.

Lemma sha512_length message : length (sha512 message) = 64.
Proof.
  unfold sha512, digest_bytes. cbn [flat_map]. rewrite !app_length, !big_endian_length.
  reflexivity.
Qed.
