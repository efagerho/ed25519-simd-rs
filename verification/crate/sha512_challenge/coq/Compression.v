From Coq Require Import List PeanoNat NArith Lia Setoid Ring.
From SHA512 Require Import Spec Facts.
Import ListNotations.

(* A single lane of the vector round. Each add wraps, including intermediate
   results. The assembly uses separate accumulators for the next a and e. *)
Local Open Scope N_scope.
Definition add64 x y := word (x + y).
Definition scheduled_round s (kw : N * N) :=
  let '(k, w) := kw in
  let hkw := add64 (h s) (add64 w k) in
  let choose := ch (e s) (f s) (g s) in
  let s1 := sum1 (e s) in
  let next_e := add64 (add64 (add64 (d s) hkw) choose) s1 in
  let t1 := add64 (add64 choose hkw) s1 in
  let next_a := add64 (add64 t1 (maj (a s) (b s) (c s))) (sum0 (a s)) in
  State next_a (a s) (b s) (c s) next_e (e s) (f s) (g s).

Local Lemma add64_left x y : word (word x + y) = word (x + y).
Proof. unfold word. apply N.add_mod_idemp_l. discriminate. Qed.
Local Lemma add64_right x y : word (x + word y) = word (x + y).
Proof. unfold word. apply N.add_mod_idemp_r. discriminate. Qed.

Local Ltac strip_words := rewrite_strat (bottomup (repeat (choice add64_left add64_right))).
Local Ltac sums :=
  unfold add64;
  strip_words;
  f_equal; ring.

Lemma scheduled_round_correct s kw : scheduled_round s kw = round s kw.
Proof. destruct kw. unfold scheduled_round, round. f_equal; sums. Qed.

(* At round t, slots t through t+15 modulo 16 hold W[t] through W[t+15].
   Consume the oldest word and replace it with W[t+16]. After 64 replacements
   the remaining 16 rounds only read the ring. *)
Local Open Scope nat_scope.
Definition slot (ring : nat -> N) t := ring (t mod 16).
Definition next_word ring t :=
  add64 (add64 (sigma0 (slot ring (t+1))) (slot ring t))
        (add64 (sigma1 (slot ring (t+14))) (slot ring (t+9))).
Definition replace_slot (ring : nat -> N) t v i :=
  if Nat.eqb i (t mod 16) then v else ring i.

Fixpoint ring_words count t ring : list N :=
  match count with
  | O => map (fun i => slot ring (t+i)) (seq 0 16)
  | S n => slot ring t :: ring_words n (S t) (replace_slot ring t (next_word ring t))
  end.

Definition represents ring t window :=
  forall i, i < 16 -> slot ring (t+i) = nth i window 0%N.

Local Lemma ring_snapshot ring t window :
  length window = 16 -> represents ring t window -> ring_words 0 t ring = window.
Proof.
  intros Len Match. cbn [ring_words].
  apply nth_ext with (d := slot ring (t+0)) (d' := 0%N).
  - now rewrite map_length, seq_length.
  - intros i Hi. rewrite map_length, seq_length in Hi.
    rewrite (map_nth (fun j => slot ring (t+j)) (seq 0 16) 0 i), seq_nth by exact Hi.
    apply Match. exact Hi.
Qed.

Local Lemma advance_window ring t w tail :
  length tail = 15 -> represents ring t (w :: tail) ->
  represents (replace_slot ring t (next_word ring t)) (S t) (tail ++ [next_word ring t]).
Proof.
  intros Len Match i Hi. unfold slot, replace_slot.
  destruct (Nat.eq_dec i 15) as [-> | Before].
  - replace (S t + 15) with (t + 1 * 16) by lia.
    rewrite Nat.mod_add, Nat.eqb_refl by lia. now rewrite <- Len, nth_middle.
  - assert (Different : (S t + i) mod 16 <> t mod 16).
    { pose proof (Nat.div_mod (S t + i) 16 ltac:(lia)).
      pose proof (Nat.div_mod t 16 ltac:(lia)). lia. }
    apply Nat.eqb_neq in Different. rewrite Different, app_nth1 by lia.
    replace (S t + i) with (t + S i) by lia. apply (Match (S i)). lia.
Qed.

Local Lemma ring_extend past window ring :
  represents ring (length past) window ->
  extend (past ++ window) (length past + 16) =
    (past ++ window) ++ [next_word ring (length past)].
Proof.
  intro Match. unfold extend, next_word.
  replace (slot ring (length past)) with (nth 0 window 0%N)
    by (rewrite <- (Nat.add_0_r (length past)) at 1; symmetry; apply Match; lia).
  rewrite !Match by lia.
  repeat rewrite app_nth2 by lia.
  replace (length past + 16 - 2 - length past) with 14 by lia.
  replace (length past + 16 - 7 - length past) with 9 by lia.
  replace (length past + 16 - 15 - length past) with 1 by lia.
  replace (length past + 16 - 16 - length past) with 0 by lia.
  f_equal. f_equal. symmetry. sums.
Qed.

Local Lemma ring_words_refine n past window ring :
  length window = 16 -> represents ring (length past) window ->
  past ++ ring_words n (length past) ring =
    fold_left extend (seq (length past + 16) n) (past ++ window).
Proof.
  revert past window ring. induction n as [|n IH]; intros past window ring Len Match.
  - cbn [seq fold_left]. now rewrite (ring_snapshot ring (length past) window Len Match).
  - destruct window as [|w tail]; [discriminate|]. cbn in Len.
    cbn [ring_words seq fold_left]. rewrite (ring_extend past (w :: tail) ring Match).
    assert (Head : slot ring (length past) = w).
    { rewrite <- (Nat.add_0_r (length past)) at 1. apply (Match 0). lia. }
    rewrite Head. set (v := next_word ring (length past)).
    specialize (IH (past ++ [w]) (tail ++ [v]) (replace_slot ring (length past) v)).
    rewrite !app_length in IH. change (length [w]) with 1 in IH.
    replace (length past + 1) with (S (length past)) in IH by lia.
    rewrite <- !app_assoc in IH. cbn [app] in IH.
    rewrite <- app_assoc. apply IH.
    + cbn. lia.
    + apply (advance_window ring (length past) w tail); auto; lia.
Qed.

Definition ring_schedule block :=
  let ws := map read_big_endian (chunks 16 8 block) in
  ring_words 64 0 (fun i => nth i ws 0%N).

Local Opaque ring_words fold_left.
Lemma ring_schedule_correct block : ring_schedule block = schedule block.
Proof.
  set (ws := map read_big_endian (chunks 16 8 block)).
  assert (Len : length ws = 16) by (unfold ws; now rewrite map_length, chunks_count).
  assert (Init : represents (fun i => nth i ws 0%N) 0 ws).
  { intros i Hi. unfold slot. cbn [Nat.add]. now rewrite Nat.mod_small. }
  exact (ring_words_refine 64 [] ws (fun i => nth i ws 0%N) Len Init).
Qed.

Local Transparent fold_left.
Theorem scheduled_rounds_correct s block :
  fold_left scheduled_round (combine constants (ring_schedule block)) s =
  fold_left round (combine constants (schedule block)) s.
Proof.
  rewrite ring_schedule_correct.
  generalize (combine constants (schedule block)) as rounds.
  intros rounds. revert s. induction rounds as [|kw rest IH]; intro s; cbn [fold_left]; auto.
  rewrite scheduled_round_correct. apply IH.
Qed.
