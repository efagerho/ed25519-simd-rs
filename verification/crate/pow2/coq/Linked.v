From Coq Require Import List ZArith.
From Machine Require execution.Blocks.
From Ed25519Simd.Pow2 Require Import Pow2Caller.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Pow2 Require Import Lane Chain Buffers Program Pow2ABI Pow2Spec.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(* Use the actual vector bodies assembled in Program.v for the arithmetic proofs. *)
Definition square_code := Blocks.fragment_code pow2_program 0.
Definition multiply_code := Blocks.fragment_code pow2_program 1.
(* Infer an arithmetic action at the first limb of each scratch save and at
   each kernel invocation. Execution.control_path_checked checks its complete
   expansion, including all ten writes of a save, for every valid entry. *)
Definition arithmetic_action (e : Blocks.effect) : list action :=
  match e with
  | Blocks.Write O (region, disp) =>
      if Nat.eqb region stack then [Store (Z.to_nat (disp / 640))] else []
  | Blocks.Evaluate O [] => [Square]
  | Blocks.Evaluate 1%nat [(8%nat, (_, disp))] => [Product (Z.to_nat (disp / 640))]
  | _ => []
  end.

Definition chain := Eval vm_compute in
  let incoming := Blocks.Control Blocks.Caller (fun _ => Blocks.Unknown) None (fun _ => None) in
  match Blocks.path 1024 pow2_program abi_layout (initial_control incoming) with
  | Some (_, es) => flat_map arithmetic_action es
  | None => []
  end.

Theorem square_refines : check_kernel true square_code = true.
Proof. vm_compute. reflexivity. Qed.
Theorem multiply_refines : check_kernel false multiply_code = true.
Proof. vm_compute. reflexivity. Qed.

Theorem linked_pow2_correct : forall a b scratch,
  pow2_spec a b (execute8 square_code multiply_code chain a b scratch).
Proof.
 apply buffers_correct; [exact square_refines | exact multiply_refines | vm_compute; reflexivity].
Qed.
