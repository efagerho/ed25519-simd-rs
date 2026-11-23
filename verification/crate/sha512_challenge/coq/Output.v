From Coq Require Import List ZArith Strings.Byte Lia.
From Machine Require Import execution.LinkedCalls memory.FlatMemory memory.ByteMemory.
From SHA512 Require Spec Facts.
Import ListNotations.
Local Open Scope Z_scope.

Definition input_bytes (m : bytes) addr n :=
  map (fun i => Spec.low_byte (Z.to_N (m (addr + Z.of_nat i)))) (seq 0 n).

Definition message_length (entry : cpu) lane :=
  read_word (mem entry) (regs entry 8%nat + 8 * Z.of_nat lane).  (* R8 *)

(* Read all five arguments at function entry. Each message length is a byte
   count. The Rust caller can supply independent lengths and aliased inputs. *)
Definition challenge_input (entry : cpu) (lane : nat) : list byte :=
  let j := Z.of_nat lane in
  let m := mem entry in
  let ptr := read_word m (regs entry 1%nat + 8*j) in       (* RCX *)
  input_bytes m (regs entry 6%nat + 32*j) 32 ++            (* RSI, R *)
  input_bytes m (regs entry 2%nat + 32*j) 32 ++            (* RDX, A *)
  input_bytes m ptr (Z.to_nat (message_length entry lane)).

(* Functional postcondition for the returning machine execution. Read physical
   bytes directly, so a word swap, byte swap, or lane swap changes the result. *)
Definition challenge_digests (entry : cpu) (after : bytes) : Prop :=
  forall lane, (lane < 8)%nat ->
    let out := regs entry 7%nat in                         (* RDI *)
    map (fun i => after (out + 64 * Z.of_nat (i / 8) + 8 * Z.of_nat lane +
                         Z.of_nat (i mod 8))) (seq 0 64) =
    map (fun b => Z.of_N (Byte.to_N b)) (Spec.sha512 (challenge_input entry lane)).

Lemma challenge_size entry lane :
  length (challenge_input entry lane) = (64 + Z.to_nat (message_length entry lane))%nat.
Proof.
  unfold challenge_input, input_bytes. rewrite !app_length, !map_length, !seq_length. lia.
Qed.

Lemma challenge_length_in_domain entry lane :
  byte_memory (mem entry) -> (Spec.bit_length (challenge_input entry lane) < 2^128)%N.
Proof.
  intro M. unfold Spec.bit_length. rewrite challenge_size. unfold message_length.
  pose proof (read_word_bound (mem entry) (regs entry 8%nat + 8 * Z.of_nat lane) M).
  unfold WordBounds.word64 in *. lia.
Qed.

Lemma challenge_padded_length entry lane :
  length (Spec.pad (challenge_input entry lane)) =
    (128 * S ((Z.to_nat (message_length entry lane) + 80) / 128))%nat.
Proof.
  rewrite Facts.padded_length, challenge_size. f_equal. f_equal. f_equal. lia.
Qed.
