From Coq Require Import List Bool PeanoNat NArith Strings.Byte Lia.
From SHA512 Require Import Spec Facts.
Import ListNotations.
Local Open Scope nat_scope.

Definition trailer (msg:list byte) :=
  let bytes := N.of_nat (length msg) in
  big_endian 8 (N.shiftr bytes 61) ++ big_endian 8 (word (N.shiftl bytes 3)).
Lemma encode_byte n x i : i<n ->
 nth i (big_endian n x) x00 = low_byte (x / 256 ^ N.of_nat (n-1-i)).
Proof.
  revert x i. induction n as [|n IH]; intros x i I; [lia|].
  cbn [big_endian]. destruct (Nat.eq_dec i n) as [->|D].
  - rewrite app_nth2, big_endian_length by (rewrite ?big_endian_length; lia).
    rewrite Nat.sub_diag. replace (S n - 1 - n) with 0 by lia. cbn. now rewrite N.div_1_r.
  - rewrite app_nth1 by (rewrite big_endian_length; lia). rewrite IH by lia.
    f_equal. rewrite N.Div0.div_div.
    replace (S n - 1 - i) with (S (n-1-i)) by lia.
    now rewrite Nat2N.inj_succ, N.pow_succ_r'.
Qed.
Local Lemma encode_mod n x : big_endian n (x mod (256^N.of_nat n)) = big_endian n x.
Proof.
  apply nth_ext with (d:=x00) (d':=x00); rewrite !big_endian_length; auto.
  intros i I. rewrite !encode_byte by exact I. unfold low_byte.
  replace (256^N.of_nat n)%N with
    ((256^N.of_nat (n-1-i)) * (256*256^N.of_nat i))%N.
  2:{ rewrite <- N.pow_succ_r', <- N.pow_add_r, <- Nat2N.inj_succ, <- Nat2N.inj_add.
      f_equal. lia. }
  set (p:= (256^N.of_nat (n-1-i))%N).
  assert (P : p <> 0%N) by (apply N.pow_nonzero; discriminate).
  rewrite N.Div0.mod_mul_r, (N.mul_comm p), N.div_add by auto.
  rewrite N.div_small by (apply N.mod_lt; auto). rewrite N.add_0_l.
  rewrite N.Div0.mod_mul_r, (N.mul_comm 256), N.mod_add, N.mod_mod by discriminate.
  reflexivity.
Qed.

Lemma trailer_correct msg : trailer msg = big_endian 16 (bit_length msg).
Proof.
  unfold trailer, bit_length, word. set (n:=N.of_nat (length msg)).
  rewrite N.shiftr_div_pow2, N.shiftl_mul_pow2.
  change (n / 2 ^ 61)%N with (n / 2305843009213693952)%N.
  replace (n*2^3)%N with (8*n)%N by apply N.mul_comm.
  change (2^64)%N with (256^N.of_nat 8)%N. rewrite encode_mod.
  apply nth_ext with (d:=x00) (d':=x00).
  - rewrite app_length, !big_endian_length. reflexivity.
  - intros i I. rewrite app_length, !big_endian_length in I.
    destruct (Nat.lt_ge_cases i 8) as [L|L].
    + rewrite app_nth1 by (rewrite big_endian_length; lia). rewrite !encode_byte by lia.
      f_equal. replace (16-1-i) with (8+(8-1-i)) by lia.
      rewrite Nat2N.inj_add, N.pow_add_r, <- N.div_div by (apply N.pow_nonzero; discriminate).
      change (256^N.of_nat 8)%N with (8*2305843009213693952)%N.
      now rewrite N.div_mul_cancel_l by discriminate.
    + rewrite app_nth2, big_endian_length by (rewrite ?big_endian_length; lia).
      rewrite !encode_byte by lia. replace (8-1-(i-8)) with (16-1-i) by lia. reflexivity.
Qed.
