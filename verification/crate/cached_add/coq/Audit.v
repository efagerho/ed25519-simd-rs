From Coq Require Import List ZArith.
From Machine Require Import execution.Blocks.
From Ed25519Simd.CachedAdd Require Import Program CachedAddBytes.

Record cached_add_contract (symbol_bytes : list Z) : Prop := {
 code_matches : image add_cached_program = symbol_bytes;
 code_valid : valid_program add_cached_program = true;
 run_concrete : forall full affine, concrete_cached_add_contract full affine add_cached_program (Z.of_nat (length symbol_bytes))
}.
Arguments code_matches {symbol_bytes} _.
Arguments code_valid {symbol_bytes} _.
Arguments run_concrete {symbol_bytes} _.
