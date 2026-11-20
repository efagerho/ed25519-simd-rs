From Coq Require Import List ZArith Strings.String.
From Machine Require Import isa.Instructions execution.MaskTrace tests.model.Oracle.
Import ListNotations. Local Open Scope Z_scope.

(* RIP-relative broadcast multiply and unsigned compare, followed by both
   outcomes of a self-KORTESTW. The comparison straddles the sign bit. *)
Definition filter_probe := [
  Op (Vector (25%nat, Load 7 0)); Op (Vector (3%nat, Load 6 0));
  Op (RipMul 18 25 35); Op (MinUnsigned 17 18 3); Op (RipLessUnsigned 4 17 26);
  Op (TestMask 4); Op (Jne8 7); Op ZeroEax; Op (Jump 4); Op (KmovEax 4); Op Return;
  Literal [3;0;0;0;0;0;0;0; 1;0;0;0;0;0;0;128]].

Definition inputs seed (j base row:nat) :=
  if Nat.eqb base 7 then
    if Z.testbit seed (Z.of_nat j) then 2^63 else 0x5555555555555555
  else if Z.testbit seed (8 + Z.of_nat j) then 0 else 2^63+1.
Definition run seed := result (program_tree 12 0 1 filter_probe 0) (inputs seed) (fun _ _=>0).
Definition seeds := [0;1;128;0x0100;0x8000;0x55aa;2^64-1].
Definition filter_report cases := String.concat "|"%string
  (numbers (bytes filter_probe) :: map (fun seed =>
     numbers (match run seed with Some m => [seed;m] | None => [] end)) cases).

Example boundaries : well_formed filter_probe = true /\
  map run seeds = map (@Some Z) [0;1;128;1;128;255;255].
Proof. vm_compute; auto. Qed.
