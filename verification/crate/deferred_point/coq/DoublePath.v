From Coq Require Import List ZArith.
From Machine Require Import execution.Blocks.
From Ed25519Simd.Double4 Require Import Double4ABI.
From Ed25519Simd.Point Require Import Double DoubleBytes.
Import ListNotations. Local Open Scope Z_scope.

Definition enter addr c := Control (At addr) (gpr c) (zf c) (return_memory c).
Definition double_entry (private:bool) incoming pad bp :=
  enter (if private then 0 else DoubleBytes.public_pc-DoubleBytes.private_pc)
        (initial_control incoming pad bp).
Definition empty_control := Control Caller (fun _=>Unknown) None (fun _=>None).
Definition double_path_data (private:bool) :=
  match path 250 Double.program abi_layout (double_entry private empty_control 0 0) with
  | Some (_,es) => es | None => [] end.
Definition double_private := Eval vm_compute in double_path_data true.
Definition double_public := Eval vm_compute in double_path_data false.
Definition double_effects (private:bool) := if private then double_private else double_public.
Definition observe (result:option (control * list effect)) := match result with
  | Some (c,es) => Some (rip c,gpr c 4%nat,es) | None=>None end.
Theorem double_path private incoming pad bp : permitted_padding pad ->
  observe (path 250 Double.program abi_layout (double_entry private incoming pad bp)) =
  Some (Caller,Ptr(scratch,1296+pad),double_effects private).
Proof. intros [<-|[<-|[<-|[<-|[]]]]]; destruct private; vm_compute; reflexivity. Qed.

Definition fragments_run (es:list effect) := flat_map
  (fun e => match e with Evaluate id _ => [id] | _=>[] end) es.
Local Open Scope nat_scope.
Definition double_pair (defer:bool) : list nat :=
  [9;10] ++ (if defer then [] else [11]) ++ [12].
Definition prepare (defer:bool) : list nat := [3;8;4;8;5;6] ++ double_pair defer ++ [7].
Definition single_round : list nat := prepare false ++ [13;1].
Theorem four_round_dispatch private :
  fragments_run (double_effects private) = [0] ++
    single_round ++ single_round ++ single_round ++ prepare private ++ [2] ++ double_pair private.
Proof. destruct private; vm_compute; reflexivity. Qed.
Theorem double_image : image Double.program = DoubleBytes.symbol_bytes /\ valid_program Double.program=true.
Proof. split; vm_compute; reflexivity. Qed.
