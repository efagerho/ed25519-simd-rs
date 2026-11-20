From Coq Require Import List ZArith Strings.String.
From Machine Require Import isa.Instructions execution.MaskTrace tests.model.Oracle.
Import ListNotations.
Local Open Scope Z_scope.

(* The first mask controls JE. The fallthrough combines two different masks.
   Keeping the literal in the image tests an actual RIP-relative qword read. *)
Definition mask_probe := [
  Op (RipBroadcast 30 61);
  Op (MemALU false 18 30 7 0); Op (MemALU true 19 30 6 0);
  Op (CompareQ 5 18 19); Op (KmovEax 5); Op (CmpEax 255); Op (Je 27);
  Op (Vector (29%nat,Load 6 64));
  Op (CompareQ 3 18 29); Op (CompareQ 4 19 29); Op (OrMask 3 4 3);
  Op (KmovEax 3); Op Return;
  Literal [0xef;0xcd;0xab;0x89;0x67;0x45;0x23;0x01]].

Definition mask_inputs seed (lane base row : nat) :=
  let bit offset := if Z.testbit seed (offset + Z.of_nat lane) then 1 else 0 in
  if Nat.eqb base 7 then bit 8 else
  if Nat.eqb row 1 then 0x0123456789abcdef + bit 24 else
  if Z.testbit seed (Z.of_nat lane) then (-bit 8) mod 2^64 else 1 + bit 16.

Definition mask_run seed := result (program_tree 16 0 2 mask_probe 0)
  (mask_inputs seed) (fun _ _ => 0).
Definition seeds := [0;0xff;0xffff;0xff7f;0xaa55;0x7e55aa81;2^64-1].
Definition mask_report inputs := String.concat "|"%string
  (numbers (bytes mask_probe) :: map (fun seed =>
    numbers (match mask_run seed with Some m => [seed;m] | None => [] end)) inputs).

Example mask_boundaries :
  well_formed mask_probe = true /\
  map mask_run [0xffff;0xff7f;0;0xaa55] = map (@Some Z) [255;0;255;85].
Proof. vm_compute; auto. Qed.
