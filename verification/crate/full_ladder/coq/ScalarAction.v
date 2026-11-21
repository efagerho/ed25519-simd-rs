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
