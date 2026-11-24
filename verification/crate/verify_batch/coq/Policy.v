(* Acceptance is stated on the original bytes. Pointer ordering, vector lanes,
   table entries, and intermediate eligibility bits do not occur here. *)
From Coq Require Import List ZArith Strings.Byte.
From Coqprime.elliptic Require GZnZ.
From Machine Require Import memory.FlatMemory memory.ByteMemory.
From ProofArithmetic Require Import Radix.
From SHA512 Require Spec.
From Curve25519 Require Import Scalar.
From Curve25519.group Require Import PrimeField Affine SignedMultiple Decompression.
Import ListNotations. Local Open Scope Z_scope.

Inductive policy := Zip215 | Dalek.

Definition byte_value b := Z.of_N (Byte.to_N b).
Definition little_endian bs := number 256 (map byte_value bs).
Definition octets (m : bytes) a n :=
  map (fun i => Spec.low_byte (Z.to_N (m (a + Z.of_nat i)))) (seq 0 n).

Record input := Input {
  key_bytes : list byte;
  r_bytes : list byte;
  s_bytes : list byte;
  message : list byte
}.

(* BatchInput is repr(C). The last word is the original output position. *)
Definition descriptor m rows i field := read_word m (rows + 40 * Z.of_nat i + field).
Definition read_input m rows i :=
  let field := descriptor m rows i in
  Input (octets m (field 0) 32) (octets m (field 8) 32)
        (octets m (field 8 + 32) 32) (octets m (field 16) (Z.to_nat (field 24))).
Definition output_index m rows i := Z.to_nat (descriptor m rows i 32).

Definition challenge input := little_endian
  (Spec.sha512 (r_bytes input ++ key_bytes input ++ message input)) mod L.

Definition decodes w P := y P = residue (w mod 2^255) /\ has_sign (Z.testbit w 255) (x P).
Definition compression P :=
  GZnZ.val Field.prime (y P) + (if parity (x P) then 2^255 else 0).

(* RFC 8032 base point. Both coordinates are their canonical representatives. *)
Definition generator := Point
  (residue 15112221349535400772501151409588531511454012693041857206046113283949847762202)
  (residue 46316835694926478169428394003475163141307993866256225615783033603165251855960)
  ltac:(apply GZnZ.zirr; vm_compute; reflexivity).

Definition signature_accepts mode input :=
  let s := little_endian (s_bytes input) in
  let r := little_endian (r_bytes input) in
  s < L /\ exists A, decodes (little_endian (key_bytes input)) A /\
    let Q := plus (scale s generator) (scale (-challenge input) A) in
    match mode with
    | Zip215 => exists R, decodes r R /\ multiple 8 (plus Q (negative R)) = identity
    | Dalek => multiple 8 A <> identity /\ r = compression Q /\ multiple 8 Q <> identity
    end.
