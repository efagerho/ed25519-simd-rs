From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.MappedFetch
 execution.ScalarBytes execution.InstructionRoute execution.QwordBlock.
From Ed25519Simd.Decode Require DecoderBytes HelperBytes Program Kernels.
Import ListNotations. Local Open Scope Z_scope.

(* Each block stops before its following CALL or RET. Its scalar projection
   is the very instruction list used by the field arithmetic proof. *)
Inductive block := Seed | Convolve | Fold | Carry | Tighten | Square.
Definition body b := match b with
 | Seed=>Kernels.seed_columns | Convolve=>Kernels.convolve | Fold=>Kernels.fold_columns
 | Carry=>Kernels.carry | Tighten=>Kernels.tighten | Square=>Kernels.square end Program.code.
Definition image b := match b with
 | Seed | Convolve | Fold=>HelperBytes.symbol_bytes | _=>DecoderBytes.symbol_bytes end.
Definition start b := match b with Seed=>0xb90 | Convolve=>0xcb0 | Fold=>0xc01
 | Carry=>0xa7e | Tighten=>0x7b7 | Square=>0x59b end.
Definition stop b := QwordBlock.after (start b) (map Arithmetic (body b)).
Lemma bytes b : linked (image b) (route (start b) (map Arithmetic (body b))).
Proof. apply checks_route;destruct b;vm_compute;reflexivity. Qed.

Theorem execute b origin s c : exists t,
 run (length (body b)) (ScalarBytes.fetch origin (image b)) (State (Running (start b)) s c)=
  Some(State (Running (stop b)) t c,[]) /\
 regs t=regs s /\ mem t=mem s /\ flag t=flag s /\
 forall j,vectors t j=Instructions.run (vector_load s j) (body b) (vectors s j).
Proof.
 destruct (QwordBlock.execute origin _ _ _ s c (bytes b)) as [t [R [G [M [F V]]]]].
 rewrite map_length in R;exists t;split;[exact R|split;[exact G|split;[exact M|split;[exact F|]]]].
 intro j;now rewrite V,arithmetic_lane.
Qed.
