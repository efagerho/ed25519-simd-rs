From Coq Require Import List ZArith.
From Machine Require Import execution.Blocks.
From Ed25519Simd.Scalar Require Import Program ScalarBytes.

Record scalar_contract (symbol_bytes : list Z) : Prop := {
 code_matches : image scalar_program = symbol_bytes;
 code_valid : valid_program scalar_program = true;
 run_concrete : concrete_scalar_contract scalar_program (Z.of_nat (length symbol_bytes))
}.
Arguments code_matches {symbol_bytes} _.
Arguments code_valid {symbol_bytes} _.
Arguments run_concrete {symbol_bytes} _.
