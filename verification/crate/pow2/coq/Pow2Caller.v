From Coq Require Import List ZArith Bool.
From Machine Require Import Instructions.
Import ListNotations.
Open Scope Z_scope.

(* Arithmetic proof summaries. Execution.v proves that the basic-block
   program executes these actions with the corresponding register and memory effects. *)
Inductive action := Store (slot:nat) | Product (slot:nat) | Square.
Definition field := nat -> Z. (* At a fixed lane, two five-limb fields. *)
Definition feed (x y:field) i :=
 if Nat.ltb i 10 then x i else
 if Nat.eqb i 28 then 19 else if Nat.eqb i 29 then 2^51-1 else
 if Nat.leb 32 i && Nat.ltb i 42 then y (i-32)%nat else x i mod 2^64.
(* The proof tracks the right operand after the 32 architectural registers
   in its symbolic environment. Only loads from R8 are admitted below. *)
Definition rhs_index (disp : Z) := (32 + Z.to_nat (disp / 64))%nat.
Definition rhs_memory (r : field) (base : nat) (disp : Z) :=
  if Nat.eqb base 8 then r (rhs_index disp) else 0.
Definition run_kernel code r := run (rhs_memory r) code r.

Definition machine := (field * (nat -> field))%type.
Definition advance sq mul op (st:machine) : machine :=
 let '(x,slots):=st in match op with
 | Store j => (x,put slots j x)
 | Square => (run_kernel sq (feed x x),slots)
 | Product j => (run_kernel mul (feed x (slots j)),slots) end.
Definition execute sq mul c (x:field) (scratch:nat -> field) :=
 fst (fold_left (fun st op=>advance sq mul op st) c (x,scratch)).

(* Each 64-byte vector occupies eight consecutive qwords in the ABI buffers. *)
Definition input_lane (a b : nat -> Z) lane i :=
  if Nat.ltb i 5 then a (i * 8 + lane)%nat
  else b ((i - 5) * 8 + lane)%nat.
Definition execute8 sq mul c a b (scratch : nat -> nat -> field) offset :=
  let lane := (offset mod 8)%nat in
  execute sq mul c (input_lane a b lane) (scratch lane) (offset / 8)%nat.

(* Operand forms used by the field refinement. *)
Definition kernel_form (op : opcode) :=
  match op with
  | MaddMem _ _ _ _ => false
  | Load base _ => Nat.eqb base 8
  | Xor a b => Nat.eqb a b
  | And _ b => Nat.eqb b 29
  | _ => true
  end.
