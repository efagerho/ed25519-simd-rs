From Coq Require Import List ZArith Bool Lia.
From Coqprime.elliptic Require GZnZ.
From Curve25519 Require Import Field Scalar.
From Curve25519.group Require Import PrimeField Affine Decompression SignedMultiple.
From Ed25519Simd.VerifyBatch Require Import Policy.
Local Open Scope Z_scope.

Definition strict mode := match mode with Zip215=>false | Dalek=>true end.
Definition eligible_input mode i :=
 little_endian (s_bytes i)<L /\ (exists R, decodes (little_endian (r_bytes i)) R) /\
 exists A, decodes (little_endian (key_bytes i)) A /\
   (strict mode=true -> multiple 8 A<>identity).

Lemma unique_key w A B : decodes w A -> decodes w B -> A=B.
Proof.
  intros [YA SA] [YB SB]. apply point_ext. split; [|congruence].
  eapply unique_signed_root; [apply on_edwards|rewrite YA,<-YB; apply on_edwards|exact SA|exact SB].
Qed.

Lemma decodes_compression Q : decodes (compression Q) Q.
Proof.
  assert (Y:0<=GZnZ.val prime (y Q)<2^255).
  { rewrite (GZnZ.inZnZ prime (y Q)). pose proof (Z.mod_pos_bound (GZnZ.val prime (y Q))
      prime ltac:(unfold prime;lia)). unfold prime in *;lia. }
  set (v:=GZnZ.val prime (y Q)) in *. unfold decodes,compression; fold v.
  assert (Rep:residue v=y Q).
  { unfold v; destruct (y Q) as [z Eq]. apply GZnZ.zirr. symmetry; exact Eq. }
  assert (Bit: forall w, Z.testbit w 255=Z.odd(w/2^255)).
  { intro w. rewrite <- Z.shiftr_div_pow2 by lia. change (Z.testbit w 255=Z.testbit (Z.shiftr w 255) 0).
    rewrite Z.shiftr_spec by lia. reflexivity. }
  rewrite Bit. destruct (parity(x Q)) eqn:P.
  - replace (v+2^255) with (v+1*2^255) by ring.
    rewrite Z.mod_add,Z.div_add,Z.mod_small,Z.div_small by lia.
    split;[congruence|right;exact P].
  - rewrite Z.add_0_r,Z.mod_small,Z.div_small by lia.
    split;[congruence|right;exact P].
Qed.

Lemma accepted_eligible mode i : signature_accepts mode i -> eligible_input mode i.
Proof.
  intros [S [A [DA Verdict]]]. split;[exact S|]. destruct mode.
  - destruct Verdict as [R [DR C]]. split;[eauto|exists A;split;[exact DA|discriminate]].
  - destruct Verdict as [Strong [Eq _]]. split;[rewrite Eq;eexists;apply decodes_compression|].
    exists A;auto.
Qed.

Definition check_point mode raw Q := match mode with
 | Zip215 => exists R, decodes raw R /\ multiple 8 (plus Q (negative R))=identity
 | Dalek => raw=compression Q /\ multiple 8 Q<>identity end.

Lemma checked_lane mode i enabled A s k :
 (enabled=true <-> eligible_input mode i) ->
 (enabled=true -> decodes (little_endian (key_bytes i)) A /\
    s=little_endian (s_bytes i) /\ k=challenge i) ->
 ((enabled=true /\ check_point mode (little_endian (r_bytes i))
   (plus (scale s generator) (scale (-k) A))) <-> signature_accepts mode i).
Proof.
 intros E Inputs. split.
 - intros [On Check]. destruct (Inputs On) as [DA [-> ->]].
   destruct (proj1 E On) as [S [_ [A' [DA' Strong]]]].
   rewrite (unique_key _ _ _ DA' DA) in Strong.
   split;[exact S|exists A;split;[exact DA|destruct mode;cbn in *;tauto]].
 - intro H. assert (On:enabled=true) by (apply E;exact (accepted_eligible _ _ H)).
   destruct (Inputs On) as [DA [-> ->]]. split;[exact On|].
   destruct H as [_ [A' [DA' H]]]. rewrite (unique_key _ _ _ DA' DA) in H.
   destruct mode;cbn in *;tauto.
Qed.
