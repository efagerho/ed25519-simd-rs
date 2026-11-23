From Machine Require Import execution.Blocks.
From Ed25519Simd.Point Require Import Double DoubleBytes Add AddBytes Frame Concrete.

Record deferred_point_contract : Prop := {
  doubling_image : image Double.program = DoubleBytes.symbol_bytes /\ valid_program Double.program=true;
  addition_image : image Add.program = AddBytes.symbol_bytes /\ valid_program Add.program=true;
  point_execution : forall k:routine, concrete_contract k
}.
