From Coq Require Import ZArith Lia Bool List.
From Machine Require Import execution.MaskTrace execution.CircuitFacts.
Local Open Scope Z_scope.
Definition byte (f:nat->bool) := mask_word 8 (fun j=>if f j then 1 else 0).
Lemma byte_range f : 0<=byte f<256.
Proof. apply mask_word_bits;intros;destruct(f j);auto. Qed.
Lemma byte_bit f j : (j<8)%nat -> Z.testbit(byte f)(Z.of_nat j)=f j.
Proof.
 intro J. assert (R:forall i,(i<8)%nat -> (if f i then 1 else 0)=0 \/ (if f i then 1 else 0)=1)
   by (intros i _;destruct(f i);auto).
 pose proof(proj2(mask_word_bits 8 _ R) j J) as H. change (Z.testbit (byte f) (Z.of_nat j)=true <-> (if f j then 1 else 0)=1) in H.
 destruct (f j), (Z.testbit (byte f) (Z.of_nat j));intuition congruence.
Qed.
Lemma above n w i : 0<=w<2^n -> n<=i -> 0<=n -> Z.testbit w i=false.
Proof.
 intros B I N;replace w with (w mod 2^n) by (apply Z.mod_small;lia).
 apply Z.mod_pow2_bits_high;lia.
Qed.
Definition score_mask xs signs ys := Z.land (Z.lnot(Z.lxor xs signs)) ys.
Definition append_mask previous matches small :=
 let shifted:=Z.shiftl previous 8 in if matches =? 0 then shifted
 else Z.land (Z.lor shifted matches) (Z.lnot small).
Lemma append_score previous (x sign y:nat->bool) small :
 0<=small<256 ->
 append_mask previous (score_mask (byte x) (byte sign) (byte y)) small =
 Z.lor (Z.shiftl previous 8) (byte (fun j=>
  (Bool.eqb (x j) (sign j) && y j) && negb(Z.testbit small (Z.of_nat j)))).
Proof.
 intro S. set (m:=score_mask (byte x) (byte sign) (byte y)).
 assert (Bit:forall j,(j<8)%nat -> Z.testbit m (Z.of_nat j)=(Bool.eqb (x j)(sign j)&&y j)%bool).
 { intros j J;unfold m,score_mask;rewrite Z.land_spec,Z.lnot_spec,Z.lxor_spec,!byte_bit by auto with zarith.
   destruct(x j),(sign j);reflexivity. }
 apply Z.bits_inj;intro i. destruct(Z_lt_ge_dec i 0);[rewrite !Z.testbit_neg_r by lia;reflexivity|].
 unfold append_mask. destruct(Z.eqb_spec m 0) as [E|E];rewrite ?Z.land_spec,?Z.lor_spec,?Z.lnot_spec by lia.
 all: destruct(Z_lt_ge_dec i 8).
 all: try (replace i with (Z.of_nat (Z.to_nat i)) by (rewrite Z2Nat.id;lia);
   rewrite Z.shiftl_spec by lia;rewrite Z.testbit_neg_r by lia;rewrite byte_bit by lia;cbn [orb]).
 - specialize(Bit (Z.to_nat i) ltac:(lia));rewrite E,Z.testbit_0_l in Bit;rewrite <-Bit;reflexivity.
 - rewrite (above 8 (byte _) i (byte_range _) ltac:(lia) ltac:(lia));symmetry;apply Bool.orb_false_r.
 - rewrite Bit by lia;reflexivity.
 - rewrite (above 8 small i S ltac:(lia) ltac:(lia)), (above 8 (byte _) i (byte_range _) ltac:(lia) ltac:(lia)).
   unfold m,score_mask;rewrite Z.land_spec,(above 8 (byte y) i (byte_range _) ltac:(lia) ltac:(lia)).
   destruct (Z.testbit _ i), (Z.testbit _ i);reflexivity.
Qed.

Definition push hi (f:nat->bool) := Z.lor (Z.shiftl hi 8) (byte f).
Lemma push_low hi f j : (j<8)%nat -> Z.testbit(push hi f)(Z.of_nat j)=f j.
Proof. intro J;unfold push;rewrite Z.lor_spec, Z.shiftl_spec, Z.testbit_neg_r, byte_bit by lia;reflexivity. Qed.
Lemma push_high hi f i : 0<=i -> Z.testbit(push hi f)(8+i)=Z.testbit hi i.
Proof. intro I;unfold push;rewrite Z.lor_spec, Z.shiftl_spec,(above 8 (byte f)) by (auto using byte_range || lia).
 replace (8+i-8) with i by ring;apply Bool.orb_false_r. Qed.
Lemma push_zero f : (forall j,(j<8)%nat -> f j=false) -> push 0 f=0.
Proof. intros F;unfold push,byte;cbn [mask_word];rewrite !F by lia;reflexivity. Qed.
