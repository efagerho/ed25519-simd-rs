From ProofArithmetic Require Import Radix.
From Coq Require Import ZArith Lia List.
From Curve25519.group Require Import Affine Representation.
From Curve25519.group Require Export SignedMultiple.
Import ListNotations. Local Open Scope Z_scope.

Definition combination s k B A := plus (scale s B) (scale (-k) A).

Lemma plus_shuffle a b c d : plus (plus a b) (plus c d)=plus (plus a c) (plus b d).
Proof. rewrite !plus_assoc; f_equal;rewrite <-!plus_assoc;f_equal;apply plus_comm. Qed.
Lemma combine_add s k t l B A : plus (combination s k B A) (combination t l B A)=
 combination (s+t) (k+l) B A.
Proof. unfold combination;rewrite plus_shuffle,<-!scale_add;f_equal;f_equal;lia. Qed.
Lemma combine_times n s k B A : multiple n (combination s k B A)=
 combination (Z.of_nat n*s) (Z.of_nat n*k) B A.
Proof. unfold combination;rewrite multiple_sum,!times_scale;f_equal;f_equal;lia. Qed.
Lemma key_only k B A : scale (-k) A=combination 0 k B A.
Proof. unfold combination;change (scale (-k) A=plus identity (scale (-k) A));now rewrite plus_identity. Qed.
Lemma base_only s B A : scale s B=combination s 0 B A.
Proof. unfold combination;change (scale s B=plus (scale s B) identity);rewrite plus_comm,plus_identity;reflexivity. Qed.

Lemma radix_step s k sl sh kl kh B A :
 ladder_sum (combination s k B A) (scale (-kh) A) (scale (sl+16*sh) B) (scale (-kl) A)
 =combination (sl+16*(sh+16*s)) (kl+16*(kh+16*k)) B A.
Proof.
 unfold ladder_sum;rewrite (key_only kh B A),(key_only kl B A),(base_only _ B A),
 !combine_times,!combine_add. f_equal;cbn [Z.of_nat];ring.
Qed.

Lemma top_pair sl sh kl kh B A :
 plus (plus (multiple 16 (scale (-kh) A)) (scale (sl+16*sh) B)) (scale (-kl) A)
 = combination (sl+16*sh) (kl+16*kh) B A.
Proof.
 rewrite (key_only kh B A),(key_only kl B A),(base_only _ B A),
 combine_times,!combine_add. f_equal;change (Z.of_nat 16) with 16;ring.
Qed.

Fixpoint remaining_digits (d:nat->Z) n := match n with
 | O=>0 | S m=>let i:=(31-m)%nat in d (2*i)%nat+16*(d (S (2*i))+16*remaining_digits d m) end.
Lemma digits_number d n : (n<=32)%nat ->
 remaining_digits d n=number 16 (map d (seq (2*(32-n)) (2*n))).
Proof.
 induction n as [|n IH];intro N;[reflexivity|].
 replace (2*S n)%nat with (S(S(2*n))) by lia.
 cbn [seq map number remaining_digits];rewrite IH by lia.
 replace (32-S n)%nat with (31-n)%nat by lia.
 replace (S (S (2*(31-n)))) with (2*(32-n))%nat by lia;reflexivity.
Qed.

(* The high pair seeds the accumulator. Each lower pair executes one Edwards
   ladder step. Digits are integers, so this also covers signed recodings. *)
Fixpoint digit_ladder (s k : nat -> Z) B A n :=
 match n with
 | O => identity
 | S m =>
     let i := (2*(31-m))%nat in
     let odd := scale (-k (S i)) A in
     let base := scale (s i+16*s (S i)) B in
     let even := scale (-k i) A in
     match m with
     | O => plus (plus (multiple 16 odd) base) even
     | S _ => ladder_sum (digit_ladder s k B A m) odd base even
     end
 end.

Lemma digit_ladder_value s k B A n :
 digit_ladder s k B A n = combination (remaining_digits s n) (remaining_digits k n) B A.
Proof.
 induction n as [|[|n] IH].
 - change (identity = plus identity identity). symmetry; apply plus_identity.
 - cbn [digit_ladder remaining_digits]. rewrite top_pair, !Z.mul_0_r, !Z.add_0_r. reflexivity.
 - change (digit_ladder s k B A (S (S n))) with
     (ladder_sum (digit_ladder s k B A (S n))
       (scale (-k (S (2*(31-S n)))) A)
       (scale (s (2*(31-S n))%nat+16*s (S (2*(31-S n)))) B)
       (scale (-k (2*(31-S n))%nat) A)).
   rewrite IH, radix_step. reflexivity.
Qed.

Lemma digit_ladder_round s k B A n : (n<31)%nat ->
 ladder_sum (digit_ladder s k B A (32-S n))
   (scale (-k (S (2*n))) A)
   (scale (s (2*n)%nat+16*s (S (2*n))) B)
   (scale (-k (2*n)%nat) A) = digit_ladder s k B A (32-n).
Proof.
 intro N. rewrite !digit_ladder_value, radix_step.
 replace (32-n)%nat with (S (32-S n)) by lia. cbn [remaining_digits].
 now replace (31-(32-S n))%nat with n by lia.
Qed.

Theorem full_ladder_value s k B A :
 digit_ladder s k B A 32 =
 combination (number 16 (map s (seq 0 64))) (number 16 (map k (seq 0 64))) B A.
Proof. rewrite digit_ladder_value, !digits_number by lia. reflexivity. Qed.
