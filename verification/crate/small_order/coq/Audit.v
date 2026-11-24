From Coq Require Import List ZArith.
From Machine Require Import execution.MaskTrace.
From Curve25519 Require Import Edwards Torsion group.Affine group.Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.SmallOrder Require Import Program.
Local Open Scope Z_scope.

Definition readable_rows (base:nat) := if Nat.eqb base 7 then 10%nat else 0%nat.
Definition inputs (p:nat->Z) (j base row:nat) := cell p row j.
Definition bounded p := forall row j, (row<10)%nat -> (j<8)%nat -> 0 <= cell p row j < 2^52.

Definition lane_result mask j q :=
  let set := Z.testbit mask (Z.of_nat j) = true in
  (set <-> torsion_roots (cx q) (cy q)) /\
  (forall P, represents_xyz q P -> (set <-> multiple 8 P = identity)).

(* Instruction budget and maximum private stack depth in bytes. *)
Definition run_at entry other pad := linked_tree 350 24 readable_rows pad entry code other helper.

(* An execution starts at the linked entry, with read-only X/Y at RDI.
   The second symbol supplies the field multiplication, root tests and
   constants reached by PC-relative instructions in that same execution. *)
Record small_order_contract (entry : Z) (entry_bytes : list Z)
                            (other : Z) (other_bytes : list Z) : Prop := {
  entry_binding : bytes code = entry_bytes /\ well_formed code = true;
  helper_binding : bytes helper = other_bytes /\ well_formed helper = true;
  linked_regions :
    0 <= entry /\ entry + Z.of_nat (length entry_bytes) < 2^64 /\
    0 <= other /\ other + Z.of_nat (length other_bytes) < 2^64 /\
    (entry + Z.of_nat (length entry_bytes) <= other \/ other + Z.of_nat (length other_bytes) <= entry);
  write_footprint : forall pad, (pad<4)%nat -> stack_writes 24 pad (linked_writes 350 24 readable_rows pad entry code other helper);
  run_correct : forall pad p initial, (pad<4)%nat -> bounded p ->
    exists mask,
      result (run_at entry other pad) (inputs p) initial = Some mask /\
      0 <= mask < 256 /\
      forall j, (j<8)%nat -> lane_result mask j (point_values p j)
}.
