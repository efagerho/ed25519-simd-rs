From Coq Require Import List ZArith.
From Machine Require Import isa.Instructions execution.Blocks.
From Ed25519Simd.CachedAdd Require Import CachedAddABI.
From Ed25519Simd.Point Require Import DoublePath Add AddBytes.
Import ListNotations. Local Open Scope Z_scope.

Inductive add_mode := Public (full affine:bool) | PrivateAffine.
Definition full m := match m with Public f _=>f | PrivateAffine=>true end.
Definition affine m := match m with Public _ a=>a | PrivateAffine=>true end.
Definition deferred m := match m with PrivateAffine=>true | _=>false end.
Definition add_entry m incoming pad bp :=
  let c := initial_control incoming pad bp (full m) (affine m) in
  match m with
  | Public _ _ => enter (AddBytes.public_pc-AddBytes.private_pc) c
  | PrivateAffine =>
    (* Only RDI and RSI are input arguments. Arbitrary incoming mode
       registers must be overwritten by the private entry instructions. *)
    Control (At 0) (put (put (gpr c) 1 (gpr incoming 1%nat)) 2 (gpr incoming 2%nat))
      (zf c) (return_memory c)
  end.
Definition add_path_data m := match path 180 Add.program (abi_layout (affine m))
  (add_entry m empty_control 0 0) with Some (_,es)=>es | None=>[] end.
Definition add_pt := Eval vm_compute in add_path_data (Public true false).
Definition add_pz := Eval vm_compute in add_path_data (Public false false).
Definition add_at := Eval vm_compute in add_path_data (Public true true).
Definition add_az := Eval vm_compute in add_path_data (Public false true).
Definition add_for_add := Eval vm_compute in add_path_data PrivateAffine.
Definition add_effects m := match m with
  | Public true false=>add_pt | Public false false=>add_pz
  | Public true true=>add_at | Public false true=>add_az | PrivateAffine=>add_for_add end.
Theorem add_path m incoming pad bp : permitted_padding pad ->
  observe (path 180 Add.program (abi_layout (affine m)) (add_entry m incoming pad bp)) =
  Some (Caller,Ptr(scratch,1296+pad),add_effects m).
Proof. intros [<-|[<-|[<-|[<-|[]]]]]; destruct m as [[] []|]; vm_compute; reflexivity. Qed.

Local Open Scope nat_scope.
Definition add_pair m : list nat := [12;13] ++ (if deferred m then [] else [14]) ++ [15].
Definition add_dispatch m : list nat :=
  [0;10;11;1] ++ (if affine m then [6;11] else [7;10;11]) ++ [2;3;4] ++ add_pair m ++
  [5] ++ (if full m then [8] ++ add_pair m else [16;9]).
Theorem add_dispatch_correct m : fragments_run (add_effects m) = add_dispatch m.
Proof. destruct m as [[] []|]; vm_compute; reflexivity. Qed.
Theorem add_image : image Add.program = AddBytes.symbol_bytes /\ valid_program Add.program=true.
Proof. split; vm_compute; reflexivity. Qed.
