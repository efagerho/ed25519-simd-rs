From Coq Require Import List ZArith.
From Machine Require Import execution.MaskTrace.
From Curve25519 Require Import Edwards Torsion group.PrimeField group.Affine group.Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Torsion Require Import Program.
Local Open Scope Z_scope.

(* Rows are 64-byte limb vectors. RDI (7) addresses P, RSI (6) addresses R. *)
Definition inputs (p r : nat -> Z) lane base row :=
  cell (if Nat.eqb base 7 then p else r) row lane.

Definition input_bounds (p r : nat -> Z) := forall i j, (i < 20)%nat -> (j < 8)%nat ->
  0 <= cell p i j < 2^52 /\ ((i < 10 \/ 15 <= i)%nat -> 0 <= cell r i j < 2^52).

(* The full arithmetic decision applies to every bounded input. Its group
   interpretation additionally requires valid extended coordinates and affine R. *)
Definition lane_result mask j q r :=
  let accepted := Z.testbit mask (Z.of_nat j) = true in
  (accepted <-> torsion_check q r) /\
  (forall P R, represents_point true q P -> represents_point true r R ->
     residue (cz r) = 1%fp -> (accepted <-> multiple 8 (plus P (negative R)) = identity)).

Record torsion_contract (symbol_bytes : list Z) : Prop := {
  code_matches : bytes code = symbol_bytes;
  code_valid : well_formed code = true;
  run_correct : forall pad p r initial, (pad < 4)%nat -> input_bounds p r ->
    exists mask,
      result (program_tree 1500 1032 20 code pad) (inputs p r) initial = Some mask /\
      0 <= mask < 256 /\
      forall j, (j < 8)%nat -> lane_result mask j (point_values p j) (point_values r j)
}.
