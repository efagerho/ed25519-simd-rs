From Coq Require Import List ZArith.
From Machine Require Import memory.FlatMemory memory.ByteMemory.
From SHA512 Require Spec.
From Ed25519 Require Export Signature.
Local Open Scope Z_scope.

Definition octets (m : bytes) a n :=
  map (fun i => Spec.low_byte (Z.to_N (m (a + Z.of_nat i)))) (seq 0 n).

Lemma octets_length m a n : length (octets m a n) = n.
Proof. unfold octets; now rewrite length_map, length_seq. Qed.

(* BatchInput is repr(C). The last word is the original output position. *)
Definition descriptor m rows i field := read_word m (rows + 40 * Z.of_nat i + field).
Definition read_input m rows i :=
  let field := descriptor m rows i in
  Input (octets m (field 0) 32) (octets m (field 8) 32)
        (octets m (field 8 + 32) 32) (octets m (field 16) (Z.to_nat (field 24)))
        (octets_length _ _ _) (octets_length _ _ _) (octets_length _ _ _).
Definition output_index m rows i := Z.to_nat (descriptor m rows i 32).
