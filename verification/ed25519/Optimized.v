From Coq Require Import ZArith Lia.
From Curve25519 Require Import Field Scalar.
From Curve25519.group Require Import PrimeField Affine SignedMultiple.
From Ed25519 Require Import Signature.
Local Open Scope Z_scope.

(* Moving [k]A across the equality works on the full Edwards group. *)
Lemma verification_point_sum s k A :
 plus (verification_point s k A) (scale k A) = scale s generator.
Proof.
 unfold verification_point, DoubleScalar.combination. rewrite plus_assoc, <-scale_add.
 replace (-k+k) with 0 by ring. change (plus (scale s generator) identity = scale s generator).
 rewrite plus_comm, plus_identity. reflexivity.
Qed.

Lemma dalek_equation s k A R :
 group_equation Dalek s k A R <-> verification_point s k A = R.
Proof.
 unfold group_equation. rewrite <-(verification_point_sum s k A). apply cancel_right_iff.
Qed.

Lemma zip215_equation s k A R :
 group_equation Zip215 s k A R <->
 multiple 8 (plus (verification_point s k A) (negative R)) = identity.
Proof.
 rewrite multiple_difference_identity. unfold group_equation.
 rewrite <-(verification_point_sum s k A), !multiple_sum. apply cancel_right_iff.
Qed.

Local Opaque multiple plus scale verification_point little_endian challenge.

Theorem signature_scoring mode i :
 signature_accepts mode i <->
 let s := little_endian (s_bytes i) in
 let r := little_endian (r_bytes i) in
 s < L /\ exists A, decodes (little_endian (key_bytes i)) A /\
   let Q := verification_point s (challenge i) A in
   match mode with
   | Zip215 => zip215_R r Q
   | Dalek => multiple 8 A <> identity /\ strict_R r Q
   end.
Proof.
 unfold signature_accepts; cbv zeta. destruct mode; split.
 - intros [S [A [DA [R [Eq DR]]]]]. apply zip215_equation in Eq.
   split; [exact S|]. exists A; split; [exact DA|now exists R].
 - intros [S [A [DA [R [DR Eq]]]]]. apply zip215_equation in Eq.
   split; [exact S|]. exists A; split; [exact DA|now exists R].
 - intros [S [A [DA [R [Eq [Bytes [Key Order]]]]]]]. apply dalek_equation in Eq.
   split; [exact S|]. exists A; split; [exact DA|]. unfold strict_R; now rewrite Eq.
 - intros [S [A [DA [Key [Bytes Order]]]]]. split; [exact S|]. exists A; split; [exact DA|].
   eexists; split; [apply dalek_equation; reflexivity|auto].
Qed.

Definition strict mode := match mode with Zip215=>false | Dalek=>true end.
Definition eligible_input mode i :=
 eligible (strict mode) (little_endian (s_bytes i)) (little_endian (key_bytes i)) (little_endian (r_bytes i)).

Lemma accepted_eligible mode i : signature_accepts mode i -> eligible_input mode i.
Proof.
  rewrite signature_scoring. intros [S [A [DA Verdict]]]. split;[exact S|]. destruct mode.
  - destruct Verdict as [R [DR C]]. split;[eauto|exists A;split;[exact DA|discriminate]].
  - destruct Verdict as [Strong [Eq _]]. split;[rewrite Eq;eexists;apply decodes_compression|].
    exists A;auto.
Qed.

Lemma checked_lane mode i enabled A s k :
 (enabled=true <-> eligible_input mode i) ->
 (enabled=true -> decodes (little_endian (key_bytes i)) A /\
    s=little_endian (s_bytes i) /\ k=challenge i) ->
 ((enabled=true /\ check_point mode (little_endian (r_bytes i))
   (verification_point s k A)) <-> signature_accepts mode i).
Proof.
 intros E Inputs. split.
 - intros [On Check]. destruct (Inputs On) as [DA [-> ->]].
   destruct (proj1 E On) as [S [_ [A' [DA' Strong]]]].
   rewrite (decodes_unique _ _ _ DA' DA) in Strong.
   apply signature_scoring. split;[exact S|exists A;split;[exact DA|destruct mode;cbn [strict check_point] in *;tauto]].
 - intro H. assert (On:enabled=true) by (apply E;exact (accepted_eligible _ _ H)).
   destruct (Inputs On) as [DA [-> ->]]. split;[exact On|].
   apply signature_scoring in H. destruct H as [_ [A' [DA' H]]]. rewrite (decodes_unique _ _ _ DA' DA) in H.
   destruct mode;cbn [strict check_point] in *;tauto.
Qed.

Theorem zip215_decoded i A R :
 little_endian (s_bytes i)<L -> decodes (little_endian (key_bytes i)) A ->
 decodes (little_endian (r_bytes i)) R ->
 (multiple 8 (plus (verification_point (little_endian (s_bytes i)) (challenge i) A) (negative R))=identity
  <-> signature_accepts Zip215 i).
Proof.
 intros S DA DR;rewrite signature_scoring;split.
 - intro H;split;[exact S|exists A;split;[exact DA|now exists R]].
 - intros [_ [A' [DA' [R' [DR' H]]]]].
   now rewrite (decodes_unique _ _ _ DA' DA),(decodes_unique _ _ _ DR' DR) in H.
Qed.

Theorem dalek_coordinates i A R :
 let r:=little_endian (r_bytes i) in let s:=little_endian (s_bytes i) in
 let Q:=verification_point s (challenge i) A in
 s<L -> decodes (little_endian (key_bytes i)) A -> multiple 8 A<>identity ->
 decodes r R -> r mod 2^255<prime -> multiple 8 R<>identity ->
 (x Q=x R /\ y Q=y R <-> signature_accepts Dalek i).
Proof.
 intros r s Q S DA Key DR Canon Strong.
 pose proof (little_endian_32 _ (r_length i)) as Width.
 rewrite signature_scoring;split.
 - intro Eq. split;[exact S|exists A;split;[exact DA|split;[exact Key|]]].
   apply (proj2 (strict_R_coordinates r R Q Width DR)). intuition congruence.
 - intros [_ [A' [DA' [_ Check]]]].
   rewrite (decodes_unique _ _ _ DA' DA) in Check.
   destruct (proj1 (strict_R_coordinates r R Q Width DR) Check) as [_ [_ XY]].
   intuition congruence.
Qed.
