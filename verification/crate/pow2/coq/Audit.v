From Coq Require Import List ZArith.
From Machine Require Import execution.Blocks.
From Ed25519Simd.Pow2 Require Import Program Pow2Bytes.

Record pow2_contract (symbol_bytes : list Z) : Prop := {
 code_matches : image pow2_program = symbol_bytes;
 code_valid : valid_program pow2_program = true;
 run_concrete : concrete_pow2_contract pow2_program (Z.of_nat (length symbol_bytes))
}.
Arguments code_matches {symbol_bytes} _.
Arguments code_valid {symbol_bytes} _.
Arguments run_concrete {symbol_bytes} _.
