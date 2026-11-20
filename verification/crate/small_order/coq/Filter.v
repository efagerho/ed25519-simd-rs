From Coq Require Import ZArith Lia Ring.
From Machine Require Import isa.Instructions execution.MaskTrace.
From Curve25519 Require Import Radix51 SmallOrderFilter.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.field51 Require Import RootMasks.
From Ed25519Simd.SmallOrder Require Import Audit Schedule.
Local Open Scope Z_scope.

Local Lemma min_word a b :
  0 <= a < 2^64 -> 0 <= b < 2^64 -> (Z.min a b) mod 2^64 = Z.min a b.
Proof. intros. apply Z.mod_small. lia. Qed.

Local Lemma add_words a b : Arithmetic.vpaddq (X86.low64 a) (X86.low64 b) = X86.low64 (a+b).
Proof. unfold Arithmetic.vpaddq, X86.low64. rewrite !Z.land_ones by lia. symmetry; apply Zplus_mod. Qed.
Local Lemma sub_words a b : Arithmetic.vpsubq (X86.low64 a) (X86.low64 b) = X86.low64 (a-b).
Proof. unfold Arithmetic.vpsubq, X86.low64. rewrite !Z.land_ones by lia. symmetry; apply Zminus_mod. Qed.
Local Lemma add_bias a : Arithmetic.vpaddq (X86.low64 a) (2^52) = X86.low64 (a + 2^52).
Proof. unfold Arithmetic.vpaddq, X86.low64. rewrite !Z.land_ones by lia. apply Zplus_mod_idemp_l. Qed.

Local Lemma four_windows m limit a b c d a' b' c' d' :
 a=a' -> b=b' -> c=c' -> d=d' ->
 (((a mod m < limit \/ b mod m < limit) \/ c mod m < limit \/ d mod m < limit) <->
  a' mod m < limit \/ b' mod m < limit \/ c' mod m < limit \/ d' mod m < limit).
Proof. intros -> -> -> ->; tauto. Qed.

(* Unroll only the 18 gates on the path to KORTESTW. Remove intermediate
   word reductions and compare the four resulting windows with the integer
   filter. This also checks the constants read from the linked image. *)
Lemma filter_lane p initial j :
  bit_spec (value j short (inputs p j) (initial j) (Wire 17))
    (small_order_candidate (fun i=>cell p i j) (fun i=>cell p (5+i)%nat j)).
Proof.
  cbv [value short operand evaluate put Nat.eqb denote inputs].
  unfold Arithmetic.vpmullq, Shift.vpsllq. rewrite Z.shiftl_mul_pow2 by lia.
  change 4503599627370496 with (2^52).
  repeat first [rewrite add_words | rewrite sub_words | rewrite add_bias].
  unfold X86.low64. rewrite !Z.land_ones by lia.
  repeat rewrite Z.mod_mod by lia.
  repeat rewrite min_word by (apply Z.mod_pos_bound; lia).
  change (9007199254740992 mod 2^64) with (2*2^52).
  match goal with |- bit_spec (if ?b then _ else _) _ =>
    assert (E : (b = true) <-> small_order_candidate (fun i=>cell p i j)
                  (fun i=>cell p (5+i)%nat j)) end.
  { rewrite Z.ltb_lt, !Z.min_lt_iff.
    unfold small_order_candidate, SmallOrderFilter.near, SmallOrderFilter.weighted,
      SmallOrderFilter.dot, SmallOrderFilter.top, SmallOrderFilter.word, SmallOrderFilter.radius.
    cbn beta. simpl Nat.add. change (Z.of_nat 13) with 13.
    (* Normalize the four integer numerators before comparing the residues. *)
    apply four_windows; ring. }
  destruct (_ <? _) eqn:B; unfold bit_spec in *; intuition discriminate.
Qed.
