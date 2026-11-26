From Coq Require Import ZArith.
From Coqprime.elliptic Require GZnZ.
From Curve25519.group Require Import PrimeField.
From Curve25519 Require Import Field Scalar.
From Curve25519.group Require Import Affine SignedMultiple DoubleScalar.
From Curve25519.group Require Export PointEncoding.
Local Open Scope Z_scope.

Inductive policy := Zip215 | Dalek.

(* RFC 8032 base point. Both coordinates are their canonical representatives. *)
Definition generator := Point
  (residue 15112221349535400772501151409588531511454012693041857206046113283949847762202)
  (residue 46316835694926478169428394003475163141307993866256225615783033603165251855960)
  ltac:(apply GZnZ.zirr; vm_compute; reflexivity).

Definition group_equation mode s k A R :=
 let left := scale s generator in
 let right := plus R (scale k A) in
 match mode with
 | Zip215 => multiple 8 left = multiple 8 right
 | Dalek => left = right
 end.

(* The ladder computes the difference once. The two scorers consume it. *)
Definition verification_point s k A := combination s k generator A.

Definition zip215_R w Q := exists R, decodes w R /\ multiple 8 (plus Q (negative R))=identity.
Definition strict_R w Q := w=compression Q /\ multiple 8 Q<>identity.

Definition check_point mode w Q := match mode with
 | Zip215 => zip215_R w Q
 | Dalek => strict_R w Q
 end.

(* Preparation decodes both points before the optimized scorer runs. *)
Definition eligible (strict:bool) s key r :=
 s<L /\ (exists R, decodes r R) /\
 exists A, decodes key A /\ (strict=true -> multiple 8 A<>identity).

(* An exact canonical match can finish a ZIP-215 lane before the torsion test. *)
Lemma canonical_zip215 w Q : w = compression Q -> zip215_R w Q.
Proof.
 intros ->. exists Q; split; [apply decodes_compression|].
 rewrite plus_negative. cbn [multiple]; now rewrite !plus_identity.
Qed.

Lemma strict_R_coordinates w R Q : 0 <= w < 2^256 -> decodes w R ->
 (strict_R w Q <-> w mod 2^255 < prime /\ multiple 8 R <> identity /\
                    (x R = x Q /\ y R = y Q)).
Proof.
 intros Width DR; split.
 - intros [Bytes Strong]. rewrite Bytes in DR.
   pose proof (decodes_unique _ _ _ DR (decodes_compression Q)) as Eq. subst R.
   rewrite Bytes, compression_y; split; [apply y_range|auto].
 - intros [Canon [Strong Coordinates]]. apply point_ext in Coordinates. subst Q.
   split; [apply canonical_decoded; assumption|exact Strong].
Qed.
