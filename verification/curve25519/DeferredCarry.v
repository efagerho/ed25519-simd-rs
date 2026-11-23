From Coq Require Import ZArith Lia Ring.
From Curve25519 Require Import Field Radix51.
Local Open Scope Z_scope.

(* One parallel radix-51 carry. The carry out of column four wraps with
   weight 19 since radix^5 = p + 19. *)
Definition carry (a:nat -> Z) (i:nat) :=
  a i mod radix +
    match i with O => 19 * (a 4%nat / radix) | S j => a j / radix end.

Lemma carry_value a : represents (limbs (carry a)) (limbs a).
Proof.
  exists (-(a 4%nat / radix)).
  assert (rem : forall i, a i mod radix = a i - radix * (a i / radix)).
  { intro i; pose proof (Z.div_mod (a i) radix ltac:(unfold radix; lia)); lia. }
  unfold limbs, carry. rewrite !rem. change prime with (radix^5-19). ring.
Qed.

Lemma carry_bound a :
  field_bound (fun _ => 2^63-1) a -> ready (carry a).
Proof.
  intros A i I. pose proof (A i I) as X.
  assert (Q : forall j, (j<5)%nat -> 0<=a j/radix<4096).
  { intros j J; specialize (A j J); split.
    - apply Z.div_pos; unfold radix; lia.
    - apply Z.div_lt_upper_bound; unfold radix; lia. }
  pose proof (Z.mod_pos_bound (a i) radix ltac:(unfold radix; lia)).
  unfold carry, ready_bound. destruct i as [|j].
  - specialize (Q 4%nat ltac:(lia)); lia.
  - specialize (Q j ltac:(lia)); lia.
Qed.

(* These five constants represent 2048*p. The cached-add instructions add
   the bias to y first, then subtract x. Bound the intermediate as well. *)
Definition subtraction_bias (i:nat) :=
  2048 * (radix - if Nat.eqb i 0 then 19 else 1).
Definition sum_columns (x y:nat -> Z) i := y i + x i.
Definition difference_columns (x y:nat -> Z) i := y i + subtraction_bias i - x i.

Theorem deferred_carry_correct x y :
  folded_columns x -> folded_columns y ->
  let sum := sum_columns x y in
  let diff := difference_columns x y in
  (forall i, (i<5)%nat ->
    0<=sum i<2^63 /\ 0<=y i+subtraction_bias i<2^63 /\ 0<=diff i<2^63) /\
  (ready (carry sum) /\ represents (limbs (carry sum)) (limbs y + limbs x)) /\
  (ready (carry diff) /\ represents (limbs (carry diff)) (limbs y - limbs x)).
Proof.
  intros X Y sum diff.
  assert (Ranges : forall i, (i<5)%nat ->
    0<=sum i<2^63 /\ 0<=y i+subtraction_bias i<2^63 /\ 0<=diff i<2^63).
  { intros i I; specialize (X i I); specialize (Y i I).
    unfold sum, diff, sum_columns, difference_columns, subtraction_bias.
    destruct (Nat.eqb i 0); unfold folded_column_bound, split, radix in *; lia. }
  split; [exact Ranges|]. split; split.
  - apply carry_bound; intros i I; specialize (Ranges i I); lia.
  - eapply ctrans; [apply carry_value|]. unfold sum, sum_columns, limbs.
    exists 0; ring.
  - apply carry_bound; intros i I; specialize (Ranges i I); lia.
  - eapply ctrans; [apply carry_value|]. exists 2048.
    unfold diff, difference_columns, subtraction_bias, limbs.
    cbn [Nat.eqb]. change prime with (radix^5-19). ring.
Qed.
