From Coq Require Import List ZArith Bool Lia.
From Curve25519 Require Import Field.
From Machine Require Import execution.MaskTrace execution.CircuitFacts.
From ProofArithmetic Require Import Expressions.
From Ed25519Simd.field51 Require Import Check RootMasks.
From Ed25519Simd.SmallOrder Require Import Program EntryBytes HelperBytes Audit.
Import ListNotations. Local Open Scope Z_scope.

Local Notation run := (run_at EntryBytes.address HelperBytes.address).
Definition paths := Eval vm_compute in run 0.
Definition short := Eval vm_compute in match paths with Branch gs _ _ _ _ => gs | _ => [] end.
Definition long := Eval vm_compute in match paths with Branch _ _ _ _ (Exit gs _ _) => gs | _ => [] end.

Lemma paths_checked pad : (pad<4)%nat ->
 run pad = Branch short (Wire 17) 0 (Exit short (Lit 0) Datatypes.tt) (Exit long (Wire 201) Datatypes.tt).
Proof. intro H; destruct pad as [|[|[|[|pad]]]]; try lia; vm_compute; reflexivity. Qed.

Definition used b row := Nat.eqb b 7 && Nat.ltb row 10.
Definition px := input_expr 7 0. Definition py := input_expr 7 5.
Definition iy := field_expr 105. Definition xx := field_expr 125.
Definition total := field_expr 168. Definition diff := field_expr 183.
Definition plan : list stage := [
 (110%nat,Cut 105 (Times (C sqrt_m1) py) FirstPositive);
 (20%nat,Cut 125 px FirstPositive);
 (43%nat,Cut 168 (Plus iy xx) (FromCarry 144 147 156));
 (15%nat,Cut 183 (minus iy xx) FirstPositive)].

Lemma exact_arithmetic : verify used plan long O (fun _=>None) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma exact_shape :
 ordered O long = true /\
 slice 130 6 long = zero_gates 105 130 /\ slice 136 6 long = zero_gates 125 136 /\
 slice 188 6 long = zero_gates 168 188 /\ slice 195 6 long = zero_gates 183 195 /\
 nth_error long 142 = Some (OrK (Wire 135) (Wire 141)) /\
 nth_error long 194 = Some (OrK (Wire 142) (Wire 193)) /\
 nth_error long 201 = Some (OrK (Wire 194) (Wire 200)).
Proof. vm_compute; repeat split. Qed.
