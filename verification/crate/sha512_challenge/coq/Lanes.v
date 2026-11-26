From Coq Require Import List PeanoNat NArith Strings.Byte Lia Bool.
From SHA512 Require Import LengthTrailer Spec Facts.
From Ed25519Simd.Sha512Challenge Require Import Block Transpose Loader.
Import ListNotations.
Local Open Scope nat_scope.

(* Read the little-endian register lane back in SHA word order. The upper
   half comes from a second call to the same transpose, with destinations 8..15. *)
Definition column_byte (msgs:nat->list byte) t lane i :=
  let first := if i <? 64 then 0 else 8 in
  let w := (i mod 64)/8 in let b := 7-i mod 8 in
  match route first (first+w) (8*lane+b) with
  | Input reg k => load_byte (msgs (reg-8)) (128*t + 8*first + k)
  | Literal n => low_byte (N.of_nat n) | Unknown => x00 end.
Definition gather_from msgs t lane (finishing:bool) tail :=
  map (fun i => if finishing && (112 <=? i)
                then nth (i-112) tail x00
                else column_byte msgs t lane i) (seq 0 128).
Definition gather msgs t lane := gather_from msgs t lane (t =? last_block (msgs lane)) (trailer (msgs lane)).
Lemma gather_correct msgs t lane : lane<8 -> gather msgs t lane = load_block (msgs lane) t.
Proof.
  intro L. unfold gather, gather_from, load_block. apply map_ext_in. intros i I. apply in_seq in I.
  unfold octet. destruct (_ && _); auto.
  unfold column_byte. assert (B:i mod 8 < 8) by (apply Nat.mod_upper_bound; lia).
  pose proof (Nat.div_mod i 64 ltac:(lia)). pose proof (Nat.mod_upper_bound i 64 ltac:(lia)).
  pose proof (Nat.div_mod (i mod 64) 8 ltac:(lia)).
  assert (E:(i mod 64) mod 8 = i mod 8).
  { change 64 with (8*8) at 1. rewrite Nat.Div0.mod_mul_r, Nat.mul_comm, Nat.Div0.mod_add.
    apply Nat.Div0.mod_mod. }
  destruct (Nat.ltb_spec i 64); rewrite transpose_bytes by (auto; lia);
    replace (8+lane-8) with lane by lia; f_equal; lia.
Qed.

Lemma nth_seq_map {A} (f:nat->A) n i d : i<n ->
  nth i (map f (seq 0 n)) d = f i.
Proof.
  intro I. rewrite nth_indep with (d':=f 0) by (rewrite map_length, seq_length; lia).
  now rewrite map_nth, seq_nth by lia.
Qed.
Definition shuffled_word x :=
  map (fun i=>low_byte (x / 256^N.of_nat (swap i mod 8))) (seq 0 8).
Definition emit s := flat_map shuffled_word (spill s).
Lemma emit_correct s : emit s = digest_bytes s.
Proof.
  assert (W : forall x, shuffled_word x = big_endian 8 x).
  { intro x. apply nth_ext with (d:=x00) (d':=x00).
    - unfold shuffled_word. now rewrite map_length, seq_length, big_endian_length.
    - intros i I. unfold shuffled_word in *. rewrite map_length, seq_length in I.
      rewrite encode_byte by exact I.
      rewrite nth_seq_map by auto.
      unfold swap. rewrite Nat.div_small, (Nat.mod_small i 8) by lia.
      change ((0 mod 2)*8) with 0. cbn [Nat.add]. now rewrite Nat.mod_small by lia. }
  unfold emit, digest_bytes, spill. now rewrite !flat_map_concat_map, (map_ext _ _ W).
Qed.

Definition transition msgs t (states:nat->state) lane :=
  block_step (states lane) (gather msgs t lane).
Definition publish msgs t states (old:nat->list byte) lane :=
  if t =? last_block (msgs lane) then emit (states lane) else old lane.
Definition more msgs t := existsb (fun lane=>t <? last_block (msgs lane)) (seq 0 8).
Definition maximum msgs := fold_right Nat.max 0 (map (fun j=>last_block (msgs j)) (seq 0 8)).
Fixpoint loop fuel msgs t states old := match fuel with
| O => None
| S n => let hs := transition msgs t states in let out := publish msgs t hs old in
         if more msgs t then loop n msgs (S t) hs out else Some out end.
Definition run_lanes msgs := loop (S(maximum msgs)) msgs 0 (fun _=>Spec.initial) (fun _=>[]).

Local Lemma maximum_bound msgs j : j<8 -> last_block (msgs j) <= maximum msgs.
Proof.
  intro J. unfold maximum. assert (H: In (last_block (msgs j))
    (map (fun k=>last_block (msgs k)) (seq 0 8))) by (apply in_map_iff; exists j; split; [reflexivity|apply in_seq; lia]).
  revert H. generalize (map (fun k=>last_block (msgs k)) (seq 0 8)).
  intros xs. induction xs; cbn; intros H; [contradiction|]. destruct H as [->|H].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IHxs, H|apply Nat.le_max_r].
Qed.
Local Lemma more_false msgs t : more msgs t = false ->
  forall j, j<8 -> last_block (msgs j) <= t.
Proof.
  intros M j J. apply Nat.nlt_ge. intro H. assert (T:more msgs t=true).
  { apply existsb_exists. exists j; split; [apply in_seq|apply Nat.ltb_lt]; lia. }
  congruence.
Qed.
Local Definition finish msg t h :=
  digest_bytes (fold_left compress (map (load_block msg) (seq t (S(last_block msg)-t))) h).
Local Lemma finish_step msg t h : t <= last_block msg ->
  finish msg t h = finish msg (S t) (compress h (load_block msg t)).
Proof.
  intro H. unfold finish. replace (S(last_block msg)-t) with (S (S(last_block msg)-S t)) by lia.
  reflexivity.
Qed.
Local Lemma finish_here msg t h : t = last_block msg ->
  finish msg t h = digest_bytes (compress h (load_block msg t)).
Proof. intros ->. unfold finish. replace (S(last_block msg)-last_block msg) with 1 by lia. reflexivity. Qed.

Local Opaque block_step compress digest_bytes emit load_block.
Local Definition remaining msgs t states old (j:nat) :=
  if last_block (msgs j) <? t then old j else finish (msgs j) t (states j).
Local Lemma progress msgs t hs old j : j<8 ->
  remaining msgs (S t) (transition msgs t hs) (publish msgs t (transition msgs t hs) old) j =
  remaining msgs t hs old j.
Proof.
  intro J. unfold remaining, publish, transition. rewrite gather_correct, block_step_correct by auto.
  destruct (Nat.ltb_spec (last_block (msgs j)) (S t)),
           (Nat.ltb_spec (last_block (msgs j)) t), (Nat.eqb_spec t (last_block (msgs j)));
    try lia; auto.
  - rewrite emit_correct, finish_here by auto. reflexivity.
  - symmetry. apply finish_step; lia.
Qed.
Local Lemma loop_result n msgs t states old :
  (forall j, j<8 -> last_block (msgs j) < t+S n) ->
  exists out, loop (S n) msgs t states old = Some out /\
    forall j, j<8 -> out j = remaining msgs t states old j.
Proof.
  revert t states old. induction n as [|n IH]; intros t hs old H;
  cbn [loop];
  destruct (more msgs t) eqn:M.
  - apply existsb_exists in M as [j [J T]]. apply in_seq in J. apply Nat.ltb_lt in T.
    specialize (H j ltac:(lia)); lia.
  - eexists; split; [reflexivity|]. intros j J. rewrite <- progress by auto.
    unfold remaining at 1. rewrite (proj2 (Nat.ltb_lt (last_block (msgs j)) (S t)) ltac:(pose proof (H j J); lia)). reflexivity.
  - destruct (IH (S t) (transition msgs t hs) (publish msgs t (transition msgs t hs) old))
      as [out [Run V]]; [intros j J; specialize (H j J); lia|].
    exists out; split; auto. intros j J. rewrite V, progress by auto. reflexivity.
  - eexists; split; [reflexivity|]. intros j J. rewrite <- progress by auto.
    symmetry. unfold remaining. rewrite (proj2 (Nat.ltb_lt (last_block (msgs j)) (S t)) ltac:(pose proof (more_false _ _ M j J); lia)).
    reflexivity.
Qed.

Local Transparent load_block.
Local Lemma load_blocks msg t n : 64 <= length msg -> t+n=S(last_block msg) ->
  map (load_block msg) (seq t n) = chunks n 128 (skipn (128*t) (pad msg)).
Proof.
  intros L. revert t. induction n as [|n IH]; intros t T; [reflexivity|].
  cbn [seq chunks map]. rewrite skipn_skipn.
  replace (128+128*t) with (128*S t) by lia. rewrite <- IH by lia.
  f_equal. unfold load_block. apply nth_ext with (d:=x00) (d':=x00).
  - rewrite map_length, seq_length, firstn_length, skipn_length, padded_size by auto. lia.
  - intros i I. rewrite map_length, seq_length in I. rewrite nth_before_cut, nth_after_skip by exact I.
    rewrite nth_seq_map by auto. apply octet_correct; lia.
Qed.
Theorem lanes_correct msgs : (forall j, j<8 -> 64 <= length (msgs j)) ->
  exists out, run_lanes msgs = Some out /\ forall j, j<8 -> out j = sha512 (msgs j).
Proof.
  intro Len. destruct (loop_result (maximum msgs) msgs 0 (fun _=>Spec.initial) (fun _=>[]))
    as [out [Run H]]; [intros j J; pose proof (maximum_bound msgs j J); lia|].
  exists out; split; auto. intros j J. rewrite H by auto. unfold remaining, finish, sha512.
  rewrite Nat.sub_0_r. rewrite load_blocks by (auto; lia).
  rewrite padded_size by auto. rewrite (Nat.mul_comm 128 (S (last_block (msgs j)))), Nat.div_mul by lia. reflexivity.
Qed.
