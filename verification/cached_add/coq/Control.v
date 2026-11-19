From Coq Require Import List ZArith Bool.
From Machine Require Import Blocks Instructions.
Require Import Program CachedAddABI.
Import ListNotations. Open Scope Z_scope.
Definition dummy := Control Caller (fun _=>Unknown) None (fun _=>None).
(* The path is computed from the byte-bound program, never supplied as an assumption. *)
Definition path_true_true := Eval vm_compute in match path 200 add_cached_program (abi_layout true)
 (initial_control dummy 0 0 true true) with Some(_,es)=>es | None=>[] end.
Definition path_true_false := Eval vm_compute in match path 200 add_cached_program (abi_layout false)
 (initial_control dummy 0 0 true false) with Some(_,es)=>es | None=>[] end.
Definition path_false_true := Eval vm_compute in match path 200 add_cached_program (abi_layout true)
 (initial_control dummy 0 0 false true) with Some(_,es)=>es | None=>[] end.
Definition path_false_false := Eval vm_compute in match path 200 add_cached_program (abi_layout false)
 (initial_control dummy 0 0 false false) with Some(_,es)=>es | None=>[] end.
Definition expected_path (full affine:bool) := if full then
 (if affine then path_true_true else path_true_false) else
 (if affine then path_false_true else path_false_false).
Definition observe_path (result:option(control * list effect)) := match result with
 | Some(c,es)=>Some(rip c,Blocks.gpr c 4%nat,es) | _=>None end.
Theorem block_layout_checked : valid_program add_cached_program=true.
Proof. vm_compute;reflexivity. Qed.
Theorem control_path_checked incoming pad bp full affine : permitted_padding pad ->
 observe_path(path 200 add_cached_program (abi_layout affine)(initial_control incoming pad bp full affine))=
 Some(Caller,Ptr(scratch,1296+pad),expected_path full affine).
Proof. intros[<- | [<- | [<- | [<- | []]]]];destruct full,affine;vm_compute;reflexivity. Qed.
