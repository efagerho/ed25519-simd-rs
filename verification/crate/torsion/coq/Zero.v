From Coq Require Import ZArith Lia Ring.
From Curve25519 Require Import Field Radix51.
Local Open Scope Z_scope.

Definition packed a b c d e := a + radix*(b + radix*(c + radix*(d + radix*e))).
Definition zero_bits a b c d e :=
  Z.land (Z.land (a+18) (Z.land b c)) (Z.land d e).

Local Lemma digit_low n : 0 <= n < 2*radix-1 ->
  Z.land n (radix-1) = radix-1 -> n = radix-1.
Proof.
 change (radix-1) with (Z.ones 51). rewrite Z.land_ones by lia.
 change (2^51) with radix. change (Z.ones 51) with (radix-1).
 pose proof (Z.div_mod n radix ltac:(unfold radix; discriminate)).
 unfold radix in *; lia.
Qed.

Local Lemma factors a b m : Z.land a b = m ->
  Z.land a m = m /\ Z.land b m = m.
Proof.
 intros <-. split.
 - rewrite Z.land_assoc, Z.land_diag. reflexivity.
 - rewrite (Z.land_comm a b), Z.land_assoc, Z.land_diag. reflexivity.
Qed.

Local Lemma split_mask a b m mask : Z.land m mask = mask ->
 Z.land a b = m -> Z.land a mask = mask /\ Z.land b mask = mask.
Proof.
 intros H F. destruct (factors _ _ _ F) as [A B].
 split; rewrite <- H at 1; rewrite Z.land_assoc; now rewrite A || rewrite B.
Qed.

(* Carries leave redundant digits. The strict lower bound on the packed
   value rules out the all-zero representation of the residue zero. *)
Theorem zero_bits_correct a b c d e :
  0 <= a < 2*radix-19 -> 0 <= b < 2*radix-1 ->
  0 <= c < 2*radix-1 -> 0 <= d < 2*radix-1 -> 0 <= e < 2*radix-1 ->
  0 < packed a b c d e < 2*prime ->
  (zero_bits a b c d e = radix-1 <-> packed a b c d e mod prime = 0).
Proof.
 intros A B C D E N. split.
 - unfold zero_bits. intro H. apply factors in H as [ABC DE].
   destruct (split_mask _ _ _ _ ABC eq_refl) as [HA BC].
   destruct (split_mask _ _ _ _ BC eq_refl) as [HB HC].
   destruct (split_mask _ _ _ _ DE eq_refl) as [HD HE].
   apply digit_low in HA, HB, HC, HD, HE; try lia.
   assert (a=radix-19) by lia. subst a b c d e. reflexivity.
 - intro M. pose proof (Z.div_mod (packed a b c d e) prime ltac:(unfold prime; discriminate)).
   assert (V : packed a b c d e = prime) by (unfold prime in *; lia).
   change prime with (packed (radix-19) (radix-1) (radix-1) (radix-1) (radix-1)) in V.
   unfold packed, radix in *. simpl Z.pow in *.
   assert (a = 2^51-19) by lia. subst a.
   assert (b = 2^51-1) by lia. subst b.
   assert (c = 2^51-1) by lia. subst c.
   assert (d = 2^51-1) by lia. subst d.
   assert (e = 2^51-1) by lia. subst e. reflexivity.
Qed.
