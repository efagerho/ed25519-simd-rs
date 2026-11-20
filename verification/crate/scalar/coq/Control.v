From Coq Require Import List ZArith Bool.
From Machine Require Import execution.Blocks memory.MemoryTrace.
From Ed25519Simd.Scalar Require Import Program ScalarABI.
Import ListNotations. Open Scope Z_scope.
Definition dummy := Control Caller(fun _=>Unknown)None(fun _=>None).
Definition expected_path := Eval vm_compute in match path 100 scalar_program abi_layout(initial_control dummy)
 with Some(_,es)=>es | None=>[]end.
Definition observe(result:option(control*list effect)) := match result with
 Some(c,es)=>Some(rip c,gpr c 4%nat,map(gpr c)saved_registers,es) | None=>None end.
Theorem block_layout_checked : valid_program scalar_program=true.
Proof. vm_compute;reflexivity. Qed.
Theorem control_checked incoming : observe(path 100 scalar_program abi_layout(initial_control incoming))=
 Some(Caller,Ptr(stack,8),map(gpr incoming)saved_registers,expected_path).
Proof. vm_compute;reflexivity. Qed.
Definition expected_events := Eval vm_compute in match record_path 100 scalar_program abi_layout(initial_control dummy)
 with Some(_,es)=>es | None=>[]end.
Theorem trace_checked incoming : option_map snd(record_path 100 scalar_program abi_layout(initial_control incoming))=
 Some expected_events.
Proof. vm_compute;reflexivity. Qed.
