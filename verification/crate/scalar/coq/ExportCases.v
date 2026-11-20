From Coq Require Import List Strings.String.
From Machine Require tests.CallerForms tests.ExportCases.
From Ed25519Simd.Scalar Require Import Program.
Import ListNotations.
Local Open Scope string_scope.

(* Fail the release conformance export if a scalar or control-flow form has
   no corresponding instruction in the native block probes. *)
Example native_caller_coverage : CallerForms.uncovered_caller_forms scalar_program = [].
Proof. vm_compute. reflexivity. Qed.

Set Printing Width 10000.
Eval vm_compute in ExportCases.exported scalar_program.
