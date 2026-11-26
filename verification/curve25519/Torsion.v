From Coq Require Import ZArith Lia.
From Curve25519 Require Import Field Radix51 Edwards.
Local Open Scope Z_scope.

(* One lane of the mixed subtraction. The right operand is affine and its
   stored Z is never read. All four comparisons are field zero tests. *)
Definition torsion_determinant q r := cx q * cy r - cy q * cx r.

Definition torsion_numerators q r :=
  let e := torsion_determinant q r in
  let h := (cy q - cx q) * (cy r + cx r) + e in
  let z := 121666 * cz q in
  let t := 121665 * (ct q * ct r) in
  (e * (z - t), (z + t) * h).

Definition torsion_roots (xx yy : Z) :=
  let iy := sqrt_m1 * yy in
  iy mod prime = 0 \/ xx mod prime = 0 \/
  (iy + xx) mod prime = 0 \/ (iy - xx) mod prime = 0.

Definition torsion_check q r :=
  let '(xx, yy) := torsion_numerators q r in torsion_roots xx yy.

Lemma determinant_zero_accepts q r :
  torsion_determinant q r mod prime = 0 -> torsion_check q r.
Proof.
  intro E. unfold torsion_check, torsion_numerators, torsion_roots. right; left.
  rewrite Z.mul_mod, E, Z.mul_0_l, Z.mod_0_l by (unfold prime; lia). reflexivity.
Qed.
