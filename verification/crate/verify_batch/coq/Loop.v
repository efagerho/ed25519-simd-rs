From Coq Require Import ZArith.
From Ed25519Simd.VerifyBatch Require Import Rows Prepare Hash ProductRun Scatter.
Local Open Scope nat_scope.

(* Geometry depends on the window and its addresses. The mask and table
   contents supplied here only instantiate the chunk record. *)
Definition make_chunk e pol bias first n :=
 Chunk e first (Nat.min n 8) pol bias (fun _ _=>false)
   (fun _=>MachineState.Data (fun _ _=>0%Z) (fun _ _=>0%Z)).
Definition spatial c := Prepare.placement c /\ Hash.geometry c /\ Hash.abi c /\ ProductRun.geometry c.
Definition entries e pol bias := forall first n, 0<n -> first+n=count e ->
 spatial (make_chunk e pol bias first n).
