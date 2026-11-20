From Coq Require Import List ZArith.
From Machine Require Import execution.Blocks.
From Ed25519Simd.Double4 Require Import Program Double4Bytes.

Record double4_contract (symbol_bytes : list Z) : Prop := {
 code_matches : image double4_program = symbol_bytes;
 code_valid : valid_program double4_program = true;
 run_concrete : concrete_double4_contract double4_program (Z.of_nat (length symbol_bytes))
}.
Arguments code_matches {symbol_bytes} _.
Arguments code_valid {symbol_bytes} _.
Arguments run_concrete {symbol_bytes} _.
