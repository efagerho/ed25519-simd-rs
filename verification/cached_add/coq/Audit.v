From Coq Require Import List ZArith.
From Machine Require Import Blocks.
Require Import Program CachedAddABI CachedAddMemory CachedAddBytes CachedAddSpec ReadFootprint.
(* Complete public certificate. Arithmetic inputs are arbitrary bounded field
   coordinates; no curve membership or consistency of cached coordinates is assumed. *)
Definition cached_add_contract(symbol_bytes:list Z) : Prop :=
 (* Every modeled instruction encodes exactly the linked symbol's bytes. *)
 image add_cached_program=symbol_bytes /\ valid_program add_cached_program=true /\
 (forall full affine initial pad,valid_cached_add_entry initial pad full affine ->exists final,
  returns add_cached_program(abi_layout affine)initial final /\
  stack_restored initial final /\ registers_preserved initial final /\
  (* One byte memory contains vectors, saved RBP and both nested return slots.
     Writes are confined to the 1280-byte point and private stack. *)
  memory_safe affine add_cached_program(Z.of_nat(length symbol_bytes))pad initial final /\
  output_initialized affine add_cached_program initial final /\
  (* Cache is preserved. Affine mode never reads beyond its 960-byte input. *)
  cache_contract affine initial final /\
  cached_add_spec full affine(words_at(memory(snd initial))point)
   (words_at(memory(snd initial))cached)(words_at(memory(snd final))point)) /\
 (* Actual pointer placements and flag qwords induce the logical entry;
    memory reads agree at every trace prefix and alignment matches AND RSP,-64. *)
 (forall full affine,concrete_cached_add_contract full affine add_cached_program
   (Z.of_nat(length symbol_bytes))).
