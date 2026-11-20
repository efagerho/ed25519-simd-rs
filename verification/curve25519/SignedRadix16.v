From Coq Require Import List ZArith Lia.
From ProofArithmetic Require Import Radix.
From Curve25519 Require Import Scalar.
Import ListNotations. Local Open Scope Z_scope.

Definition bias n := number 16 (repeat 8 n).
Definition nibble x i := x / 16^(Z.of_nat i) mod 16.
Definition digit x i := nibble (x+bias 64) i - 8.
Definition signed_byte b := if b <? 128 then b else b-256.

Lemma digit_range x i : -8 <= digit x i < 8.
Proof. unfold digit,nibble; pose proof (Z.mod_pos_bound ((x+bias 64)/16^Z.of_nat i) 16); lia. Qed.
Lemma signed_encoding d : -8<=d<8 -> signed_byte (d mod 256)=d.
Proof.
 intro B; unfold signed_byte; destruct (Z_lt_ge_dec d 0).
 - replace (d mod 256) with (d+256) by (apply Z.mod_unique with (-1); [left;lia|ring]).
   destruct (d+256 <? 128) eqn:T; try apply Z.ltb_lt in T; lia.
 - rewrite Z.mod_small by lia. destruct (d<?128) eqn:T; [reflexivity|apply Z.ltb_ge in T; lia].
Qed.

Local Lemma positional n x i :
 number 16 (map (digit x) (seq i n)) + bias n =
 ((x+bias 64)/16^Z.of_nat i) mod 16^Z.of_nat n.
Proof.
 revert i; induction n; intro i; [cbn [seq map number bias repeat]; now rewrite Z.mod_1_r|].
 change (digit x i + 16*number 16 (map (digit x) (seq (S i) n)) +
   (8+16*bias n) = ((x+bias 64)/16^Z.of_nat i) mod 16^Z.of_nat (S n)).
 unfold digit at 1; unfold nibble.
 replace ( (x+bias 64)/16^Z.of_nat i mod 16 - 8 +
  16*number 16 (map (digit x) (seq (S i) n)) + (8+16*bias n))
  with ((x+bias 64)/16^Z.of_nat i mod 16 +
       16*(number 16 (map (digit x) (seq (S i) n))+bias n)) by ring.
 rewrite IHn, !Nat2Z.inj_succ, !Z.pow_succ_r by lia.
 rewrite (Z.mul_comm 16 (16^Z.of_nat i)), <-Z.div_div by (try apply Z.pow_pos_nonneg;lia).
 set (q:=(x+bias 64)/16^Z.of_nat i).
 assert(P:0<16^Z.of_nat n) by (apply Z.pow_pos_nonneg;lia).
 pose proof(Z.div_mod q 16 ltac:(lia)).
 pose proof(Z.div_mod (q/16) (16^Z.of_nat n) ltac:(lia)).
 pose proof(Z.mod_pos_bound q 16 ltac:(lia)).
 pose proof(Z.mod_pos_bound (q/16) _ P).
 apply Z.mod_unique with (q/16/16^Z.of_nat n); [left;lia|nia].
Qed.
Lemma reconstruct x : canonical_scalar x -> number 16 (map (digit x) (seq 0 64))=x.
Proof.
 intro H; pose proof(positional 64 x 0) as E.
 change (number 16 (map (digit x) (seq 0 64))+bias 64=(x+bias 64)/1 mod 16^64) in E.
 rewrite Z.div_1_r,Z.mod_small in E; [lia|].
 unfold canonical_scalar in H. change (0<=x+0x8888888888888888888888888888888888888888888888888888888888888888<2^256). unfold L in H; lia.
Qed.
