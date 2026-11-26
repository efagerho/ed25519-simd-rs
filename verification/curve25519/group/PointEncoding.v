(* Integer encoding of an Edwards point in 255 y bits and one x-sign bit. *)
From Coq Require Import ZArith Lia.
From Coqprime.elliptic Require GZnZ.
From Curve25519 Require Import Field.
From Curve25519.group Require Import PrimeField Affine Decompression Cofactor.
Local Open Scope Z_scope.
Local Notation val := (GZnZ.val prime).

Definition decodes w P := y P = residue (w mod 2^255) /\ has_sign (Z.testbit w 255) (x P).
Definition compression P :=
  GZnZ.val Field.prime (y P) + (if parity (x P) then 2^255 else 0).

Lemma signed_encoding w :
 (exists u, on_curve u (residue (w mod 2^255))) <-> exists P, decodes w P.
Proof.
 set (v := residue (w mod 2^255)).
 split.
 - intros [u U]. pose proof (decode_correct v (Z.testbit w 255)) as D.
   destruct (decode v (Z.testbit w 255)) as [z|].
   + destruct D as [C S]. exists (Point z v C); split; [reflexivity|exact S].
   + contradiction (D u U).
 - intros [P [Y _]]. exists (x P); fold v in Y; rewrite <-Y; apply on_edwards.
Qed.

Lemma decodes_unique w A B : decodes w A -> decodes w B -> A=B.
Proof.
  intros [YA SA] [YB SB]. apply point_ext. split; [|congruence].
  eapply unique_signed_root; [apply on_edwards|rewrite YA,<-YB; apply on_edwards|exact SA|exact SB].
Qed.

Lemma y_range P : 0 <= val (y P) < prime.
Proof. rewrite (GZnZ.inZnZ prime (y P)); apply Z.mod_pos_bound; unfold prime; lia. Qed.

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

Lemma compression_y P : compression P mod 2^255 = val (y P).
Proof.
 pose proof (y_range P).
 unfold compression. destruct (parity (x P)).
 - replace (val (y P)+2^255) with (val (y P)+1*2^255) by ring.
   rewrite Z.mod_add by lia. apply Z.mod_small; unfold prime in *; lia.
 - rewrite Z.add_0_r. apply Z.mod_small; unfold prime in *; lia.
Qed.

Lemma strict_encoding_y_range P : multiple 8 P <> identity ->
  1 < compression P mod 2^255 < prime-1.
Proof.
 intro Strong.
 pose proof (y_range P) as Range.
 rewrite compression_y.
 assert (Y0:y P <> 0%fp).
 { intro Y;apply Strong,eight_identity_iff;rewrite Y;ring. }
 assert (Unit:y P <> 1%fp /\ y P <> (0-1)%fp).
 { assert (Weak: y P=1%fp \/ y P=(0-1)%fp -> False).
   { intro Y. assert (Zero:on_curve 0%fp (y P)).
     { destruct Y as [-> | ->];unfold on_curve;ring. }
     assert (X:x P=0%fp).
     { eapply (unique_signed_root (parity(x P)) _ _ (y P));
       [apply on_edwards|exact Zero|right;reflexivity|left;reflexivity]. }
     apply Strong,eight_identity_iff;rewrite X;ring. }
   tauto. }
 destruct Unit as [Y1 Ym].
 assert (ValEq:forall a b:fp, val a=val b -> a=b) by (intros [a A] [b B];apply GZnZ.zirr).
 assert (val(y P)<>0) by (intro E;apply Y0,ValEq;exact E).
 assert (val(y P)<>1) by (intro E;apply Y1,ValEq;exact E).
 assert (val(y P)<>prime-1) by (intro E;apply Ym,ValEq;exact E).
 lia.
Qed.

Lemma compression_parts w P : 0<=w<2^256 ->
 (w=compression P <-> w mod 2^255=val(y P) /\ Z.testbit w 255=parity(x P)).
Proof.
 intro Bound.
 pose proof (y_range P) as Range.
 change (0<=w<2^256) in Bound. assert (Hi:0<=w/2^255<2) by (split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia).
 pose proof(Z.div_mod w (2^255) ltac:(discriminate)).
 pose proof(Z.mod_pos_bound w (2^255) ltac:(lia)).
 replace (Z.testbit w 255) with (Z.odd (w/2^255)) by (rewrite <-Z.shiftr_div_pow2 by lia;change (Z.testbit (Z.shiftr w 255) 0=Z.testbit w 255);rewrite Z.shiftr_spec by lia;reflexivity). unfold compression. destruct(parity(x P));
 destruct (Z.eq_dec (w/2^255) 0) as [Q|N]; try assert (Q:w/2^255=1) by lia;
 rewrite Q; cbn [Z.odd];unfold prime in *;intuition lia.
Qed.

Lemma canonical_decoded w P : 0<=w<2^256 -> decodes w P ->
 w mod 2^255<prime -> multiple 8 P<>identity -> w=compression P.
Proof.
 intros Bound [Y Sign] Canon Strong. apply (proj2 (compression_parts w P Bound)).
 split.
 - rewrite Y. change (w mod 2^255=(w mod 2^255) mod prime).
   rewrite (Z.mod_small _ prime); [reflexivity|pose proof (Z.mod_pos_bound w (2^255) ltac:(lia));lia].
 - destruct Sign as [X|Parity]; [exfalso;apply Strong,eight_identity_iff;rewrite X;ring|symmetry;exact Parity].
Qed.
