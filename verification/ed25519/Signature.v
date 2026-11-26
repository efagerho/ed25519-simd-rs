(* Both policies hash the original encodings, including accepted noncanonical keys. *)
From Coq Require Import List ZArith Lia Strings.Byte.
From ProofArithmetic Require Import Radix.
From SHA512 Require Spec.
From Curve25519 Require Import Scalar.
From Curve25519.group Require Import Affine.
From Ed25519 Require Export Equations.
Import ListNotations. Local Open Scope Z_scope.

Definition byte_value b := Z.of_N (Byte.to_N b).
Definition little_endian bs := number 256 (map byte_value bs).

Record input := Input {
  key_bytes : list byte;
  r_bytes : list byte;
  s_bytes : list byte;
  message : list byte;
  key_length : length key_bytes = 32%nat;
  r_length : length r_bytes = 32%nat;
  s_length : length s_bytes = 32%nat
}.

Definition challenge input := little_endian
  (Spec.sha512 (r_bytes input ++ key_bytes input ++ message input)) mod L.

Definition signature_accepts mode input :=
  let s := little_endian (s_bytes input) in
  let r := little_endian (r_bytes input) in
  s < L /\ exists A, decodes (little_endian (key_bytes input)) A /\
    exists R, group_equation mode s (challenge input) A R /\
      match mode with
      | Zip215 => decodes r R
      | Dalek => r = compression R /\ multiple 8 A <> identity /\ multiple 8 R <> identity
      end.

Lemma little_endian_32 bs : length bs = 32%nat -> 0 <= little_endian bs < 2^256.
Proof.
 intro Width. unfold little_endian.
 assert (Digits : Forall (fun x => 0 <= x < 256) (map byte_value bs)).
 { apply Forall_forall. intros x H; apply in_map_iff in H as [b [<- _]].
   unfold byte_value. pose proof (Byte.to_N_bounded b); lia. }
 pose proof (number_bound 256 _ ltac:(lia) Digits) as Bound.
 rewrite length_map, Width in Bound. exact Bound.
Qed.
