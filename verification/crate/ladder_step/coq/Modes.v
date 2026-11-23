From Coq Require Import ZArith List.
From Machine Require Import execution.LinkedCalls.
From Ed25519Simd.CachedAdd Require CachedAddABI.
From Ed25519Simd.LadderStep Require Export PointMode.
Import ListNotations. Local Open Scope Z_scope.
Definition defer_add (f a:bool) := if a then if f then defer_double else false else false.
Definition add_offset f a := if defer_add f a then 0 else public_add_offset.
Definition add_target base f a := base + add_offset f a.
Definition mode_args f a (s:cpu) := if defer_add f a then True else
  regs s 2%nat=CachedAddABI.flag_word f /\ regs s 1%nat=CachedAddABI.flag_word a.
Definition affine_setup : list command := if defer_double then [] else [Immediate 2 1;Immediate 1 1].
Definition setup_length := if defer_double then 0 else 10.
