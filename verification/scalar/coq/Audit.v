From Coq Require Import List ZArith.
From Machine Require Import Blocks.
Require Import Program ScalarABI ScalarSpec ScalarMemory ScalarBytes.

(* One complete public contract. The byte-memory clause constructs the
   logical entry from actual pointer qwords, vector qwords and bytes. *)
Definition scalar_contract (symbol_bytes : list Z) : Prop :=
  (* The instruction model encodes exactly the linked function. *)
  image scalar_program = symbol_bytes /\
  valid_program scalar_program = true /\
  (* Every unsigned 512-bit input is covered; there is no limb-bound premise. *)
  (forall initial, valid_scalar_entry initial -> exists final,
    returns scalar_program abi_layout initial final /\
    stack_restored initial final /\
    registers_preserved initial final /\
    memory_safe scalar_program (Z.of_nat (length symbol_bytes)) initial final /\
    output_initialized scalar_program initial final /\
    scalar_spec
      (words_at (memory (snd initial)) input)
      (words_at (memory (snd final)) output)) /\
  (* Actual byte reads agree at every prefix, all 320 output bytes are
     written, and every byte outside output is preserved. *)
  concrete_scalar_contract scalar_program (Z.of_nat (length symbol_bytes)).
