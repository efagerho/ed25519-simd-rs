From Coq Require Import ZArith Lia.
From Curve25519 Require Import Field Radix51 Torsion.
Local Open Scope Z_scope.

(* The assembly computes these estimates modulo one 64-bit word. *)
Local Definition word := 2^64.
Local Definition radius := 2^52.
Local Definition top (x : nat -> Z) := 2^13 * x 4%nat.
Local Definition dot a b c d e (y : nat -> Z) :=
  a*y 0%nat + b*y 1%nat + c*y 2%nat + d*y 3%nat + e*y 4%nat.

(* Each weight is the nearest integer to word * ((i * radix^j) mod p) / p.
   The error proof below checks the literal constants used in assembly. *)
Local Definition weighted := dot 0x570649009f83be16 0xf0b2b4d00993dfbd
  0xfdebd397a18c0357 0x1ab4bf91e313b86d 0xc364e941d416ceaf.
Local Definition near (z : Z) := (z + radius) mod word < 2 * radius.

Definition small_order_candidate x y :=
  near (weighted y) \/ near (top x) \/
  near (weighted y + top x) \/ near (weighted y - top x).

(* Restore the whole words discarded from the estimate of i*Y. *)
Local Definition period j := sqrt_m1 * radix^j / prime.
Local Definition periods := dot (period 0) (period 1) (period 2) (period 3) (period 4).

Local Ltac digit_bounds H :=
  let take j := let B := fresh "B" in
    pose proof (H j ltac:(lia)) as B; unfold split in B in
  take 0%nat; take 1%nat; take 2%nat; take 3%nat; take 4%nat.

Local Lemma top_error x : split_field x ->
  0 <= word * limbs x - prime * top x < prime * 2^16.
Proof.
  intro H. digit_bounds H. unfold limbs, top, prime, word, radix. lia.
Qed.

Local Lemma weighted_error y : split_field y ->
  let error := word * (sqrt_m1 * limbs y) - prime * (weighted y + word * periods y) in
  -(prime * (radius - 2^16)) < error < prime * (radius - 2^16).
Proof.
  intro H. digit_bounds H. unfold periods.
  repeat match goal with |- context[period ?j] =>
    let q := eval vm_compute in (period j) in change (period j) with q end.
  unfold weighted, dot, limbs, radix, sqrt_m1, prime, word, radius. lia.
Qed.

Local Lemma near_multiple z k :
  -(prime * radius) < prime * (z - k * word) < prime * radius -> near z.
Proof.
  unfold near, prime, radius, word. intro E.
  replace (z + 2^52) with ((z + 2^52 - k * 2^64) + k * 2^64) by ring.
  rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.

(* A lane satisfying any exact root test always reaches the exact check,
   even with noncanonical or independently maximal 52-bit limbs. *)
Theorem small_order_filter_sound x y :
  split_field x -> split_field y ->
  torsion_roots (limbs x) (limbs y) -> small_order_candidate x y.
Proof.
  intros X Y. pose proof (top_error x X) as A. pose proof (weighted_error y Y) as B.
  cbv zeta in B. unfold torsion_roots, small_order_candidate.
  intros [E | [E | [E | E]]]; apply Z.mod_divide in E as [k E]; try (unfold prime; lia).
  - left. apply (near_multiple _ (k - periods y)). unfold prime, word, radius in *. lia.
  - right; left. apply (near_multiple _ k). unfold prime, word, radius in *. lia.
  - right; right; left. apply (near_multiple _ (k - periods y)). unfold prime, word, radius in *. lia.
  - right; right; right. apply (near_multiple _ (k - periods y)). unfold prime, word, radius in *. lia.
Qed.
