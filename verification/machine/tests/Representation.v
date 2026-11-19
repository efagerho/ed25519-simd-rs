From Coq Require Import ZArith List Lia.
From Machine Require Import Blocks FlatMemory WordBounds ByteMemory Shift.
Import ListNotations.
Open Scope Z_scope.

(* Regression for the review's counterexample: serialized equality alone
   loses high bits, while the representability predicate excludes them. *)
Example serialization_requires_word_bound :
 map (word_byte 0) [0;1;2;3;4;5;6;7] =
 map (word_byte (2^64)) [0;1;2;3;4;5;6;7] /\
 vpsrlq 0 64 <> vpsrlq (2^64) 64 /\ ~ word64 (2^64).
Proof. vm_compute; intuition discriminate. Qed.

Example little_endian_high_bit :
 read_word (fun a => if a =? 7 then 128 else 0) 0 = 2^63 /\
 read_word (fun _ => 255) 0 = 2^64-1.
Proof. vm_compute; auto. Qed.

Example unaligned_store_lanes_and_guards :
 let after := write_bytes (fun _ => 0xab) 3 64 (vector_byte (fun j => 2^63+Z.of_nat j)) in
 read_word after 3 = 2^63 /\ read_word after 59 = 2^63+7 /\
 after 2 = 0xab /\ after 67 = 0xab.
Proof. vm_compute; auto. Qed.

Example reject_negative_lane :
 ~ data_words (Data (fun _ _ => -1) (fun _ _ => 0)).
Proof. intros [R _]; specialize (R 0%nat 0%nat ltac:(lia)); unfold word64 in R; cbn in R; lia. Qed.
Example reject_non_byte_memory : ~ byte_memory (fun _ => 256).
Proof. intro H; specialize (H 0); lia. Qed.
