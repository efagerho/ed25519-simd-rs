From Coq Require Import List ZArith.
From Machine Require Import execution.Blocks.
From Ed25519Simd.Double4 Require Import Double4ABI.
From Ed25519Simd.Point Require Import Double DoubleBytes DoublePath Add AddBytes AddPath.
From Ed25519Simd.CachedAdd Require CachedAddABI.
Import ListNotations. Local Open Scope Z_scope.

Record deferred_point_contract : Prop := {
  doubling_image : image Double.program = DoubleBytes.symbol_bytes /\ valid_program Double.program=true;
  doubling_returns : forall private incoming pad bp, permitted_padding pad ->
    observe (path 250 Double.program abi_layout (double_entry private incoming pad bp)) =
    Some (Caller,Ptr(scratch,1296+pad),double_effects private);
  doubling_rounds : forall private, fragments_run (double_effects private) =
    [0%nat] ++ single_round ++ single_round ++ single_round ++ prepare private ++ [2%nat] ++ double_pair private;
  addition_image : image Add.program = AddBytes.symbol_bytes /\ valid_program Add.program=true;
  addition_returns : forall m incoming pad bp, permitted_padding pad ->
    observe (path 180 Add.program (CachedAddABI.abi_layout (affine m)) (add_entry m incoming pad bp)) =
    Some (Caller,Ptr(scratch,1296+pad),add_effects m);
  addition_branches : forall m, fragments_run (add_effects m) = add_dispatch m
}.
