From Coq Require Import List PeanoNat NArith Lia.
From SHA512 Require Import Spec.
From Ed25519Simd.Sha512Challenge Require Import Compression Rounds.
Import ListNotations.
Local Open Scope nat_scope.

(* R10 advances by 16 qwords after each expanding body. *)
Definition key t i := nth (t - t mod 16 + i) constants 0%N.
Fixpoint run_with table count expanding t regs := match count with
| O => regs
| S n => run_with table n expanding (S t) (execute expanding t
    (fun i => nth (t-t mod 16+i) table 0%N) regs) end.
Definition run := run_with constants.

Definition first_words block := map read_big_endian (chunks 16 8 block).
Definition spill s := [a s;b s;c s;d s;e s;f s;g s;h s].
Definition load_regs s block i :=
  if i <? 16 then nth i (first_words block) 0%N else nth (i-16) (spill s) 0%N.
Definition feed s v :=
  State (add64 (a v) (a s)) (add64 (b v) (b s))
        (add64 (c v) (c s)) (add64 (d v) (d s))
        (add64 (e v) (e s)) (add64 (f v) (f s))
        (add64 (g v) (g s)) (add64 (h v) (h s)).
Definition working_with table s block :=
  let expanded := length table - 16 in view (expanded+16)
  (run_with table 16 false expanded (run_with table expanded true 0 (load_regs s block))).
Definition working := working_with constants.
Definition block_step s block := feed s (working s block).

Local Definition agree (r w:nat->N) := forall i, i < 16 -> r i = w i.
Local Lemma word_agree r w t : agree r w -> next_word r t = next_word w t.
Proof. intro H. unfold next_word, slot. now rewrite !H by (apply Nat.mod_upper_bound; lia). Qed.
Local Lemma advance ex t r w : agree r w -> agree (execute ex t (key t) r)
  (if ex then replace_slot w t (next_word w t) else w).
Proof.
  intros H i I. rewrite round_ring by assumption. destruct ex; auto.
  unfold replace_slot. destruct (i =? t mod 16); auto using word_agree.
Qed.
Local Lemma key_at t : key t (t mod 16) = nth t constants 0%N.
Proof. unfold key. f_equal. apply Nat.sub_add. apply Nat.mod_le; lia. Qed.
Local Definition keys t n := map (fun i => nth i constants 0%N) (seq t n).

Local Lemma final_rounds n t r w : agree r w ->
  view (t+n) (run n false t r) =
  fold_left scheduled_round (combine (keys t n) (map (slot w) (seq t n))) (view t r).
Proof.
  revert t r. induction n as [|n IH]; intros t r H.
  - now rewrite Nat.add_0_r.
  - change (run (S n) false t r) with (run n false (S t) (execute false t (key t) r)). cbn [keys seq map combine fold_left]. replace (t+S n) with (S t+n) by lia.
    rewrite (IH (S t) _ (advance false t r w H)), round_state, key_at.
    unfold slot. rewrite H by (apply Nat.mod_upper_bound; lia). reflexivity.
Qed.

Local Lemma seq_offset t n : seq t n = map (Nat.add t) (seq 0 n).
Proof.
  apply nth_ext with (d:=t) (d':=t).
  - now rewrite map_length, !seq_length.
  - intros i H. rewrite seq_length in H. rewrite seq_nth by exact H.
    replace (nth i (map (Nat.add t) (seq 0 n)) t) with (nth i (map (Nat.add t) (seq 0 n)) (t+0)) by now rewrite Nat.add_0_r.
    rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

Local Lemma all_rounds n t r w : agree r w ->
  view (t+n+16) (run 16 false (t+n) (run n true t r)) =
  fold_left scheduled_round (combine (keys t (n+16)) (ring_words n t w)) (view t r).
Proof.
  revert t r w. induction n as [|n IH]; intros t r w H.
  - rewrite Nat.add_0_r. change (run 0 true t r) with r.
    rewrite (final_rounds 16 t r w H). cbn [ring_words]. f_equal.
    f_equal. rewrite (seq_offset t 16) at 1. rewrite map_map. reflexivity.
  - change (run (S n) true t r) with (run n true (S t) (execute true t (key t) r)).
    replace (t+S n) with (S t+n) by lia.
    rewrite (IH (S t) _ _ (advance true t r w H)), round_state, key_at.
    cbn [ring_words keys Nat.add seq map combine fold_left].
    unfold slot at 1. rewrite H by (apply Nat.mod_upper_bound; lia). reflexivity.
Qed.

Local Opaque run ring_words fold_left.
Theorem block_step_correct s block : block_step s block = compress s block.
Proof.
  set (w := fun i => nth i (first_words block) 0%N).
  assert (H : agree (load_regs s block) w).
  { intros i I. unfold load_regs, w. now rewrite (proj2 (Nat.ltb_lt _ _) I). }
  pose proof (all_rounds 64 0 (load_regs s block) w H) as C.
  change (view 80 (run 16 false 64 (run 64 true 0 (load_regs s block))) =
    fold_left scheduled_round (combine (keys 0 80) (ring_schedule block)) (view 0 (load_regs s block))) in C.
  assert (K : keys 0 80 = constants) by (vm_compute; reflexivity).
  assert (V : view 0 (load_regs s block) = s) by (destruct s; reflexivity).
  unfold block_step. change (working s block) with (view 80 (run 16 false 64 (run 64 true 0 (load_regs s block)))). rewrite C, K, V, scheduled_rounds_correct. unfold compress, feed, add64.
  now rewrite !(N.add_comm _ (_ s)).
Qed.
