From Coq Require Import ZArith.
From Curve25519 Require Import Field Radix51Digits DecompressionRadix51.
From Curve25519.group Require Import PrimeField Decompression.
Local Open Scope Z_scope.

(* The biased integer columns used by both decoders give the two field
   elements in the Edwards square-root criterion. *)
Lemma setup_field h y : represents (pack h) (y*y) ->
 residue (pack (u_digits h)) = numerator (residue y) /\
 residue (pack (v_digits h)) = denominator (residue y).
Proof.
 intro YY. destruct (setup_digits _ _ YY) as [U V].
 apply congruent_value in U,V. unfold denominator,numerator.
 rewrite U,V; repeat rewrite residue_sub; repeat rewrite residue_mul;
 repeat rewrite residue_sub; now repeat rewrite residue_mul.
Qed.
