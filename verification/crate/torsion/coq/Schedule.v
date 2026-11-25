From Coq Require Import List ZArith Lia Bool.
From ProofArithmetic Require Import Interval.
From Curve25519 Require Import Field.
From Machine Require Import execution.MaskTrace execution.CircuitFacts.
From Ed25519Simd.Torsion Require Import Program.
From Ed25519Simd.field51 Require Import Check.
Import ListNotations. Local Open Scope Z_scope.

Definition input_used b i := (Nat.eqb b 7 || (Nat.eqb b 6 && (Nat.ltb i 10 || Nat.leb 15 i))) && Nat.ltb i 20.

Definition paths := Eval vm_compute in program_tree 1500 1032 20 code 0.
Definition long := Eval vm_compute in match paths with Branch _ _ _ _ (Exit gs _ _)=>gs | _=>[] end.
Definition short := Eval vm_compute in firstn 166 long.

Lemma paths_checked pad : (pad<4)%nat ->
 program_tree 1500 1032 20 code pad =
 Branch short (Wire 165) 255 (Exit short (Wire 165) Datatypes.tt) (Exit long (Wire 822) Datatypes.tt).
Proof. intros H; destruct pad as [|[|[|[|pad]]]]; try lia; vm_compute; reflexivity. Qed.

(* Each cut names the five output wires after a parallel carry. The first
   limb is written last. The checker reconstructs the computation between
   cuts from the decoded instructions, including all nested calls. *)
Definition px:=input_expr 7 0. Definition py:=input_expr 7 5.
Definition pz:=input_expr 7 10. Definition pt:=input_expr 7 15.
Definition rx:=input_expr 6 0. Definition ry:=input_expr 6 5. Definition rt:=input_expr 6 15.
Definition det:=field_expr 155. Definition dy:=field_expr 191. Definition sy:=field_expr 206.
Definition h:=field_expr 303. Definition tt:=field_expr 395.
Definition g:=field_expr 455. Definition f:=field_expr 470.
Definition xx:=field_expr 562. Definition yy:=field_expr 654. Definition iy:=field_expr 746.
Definition sum:=field_expr 789. Definition diff:=field_expr 804.
Definition plan : list stage := [
 (160%nat,Cut 155 (minus (Times px ry) (Times py rx)) FirstPositive);
 (36%nat,Cut 191 (minus py px) NoLower);
 (15%nat,Cut 206 (Plus ry rx) NoLower);
 (97%nat,Cut 303 (Plus (Times dy sy) det) NoLower);
 (92%nat,Cut 395 (Times pt rt) NoLower);
 (60%nat,Cut 455 (Plus (Times (C 121666) pz) (Times (C 121665) tt)) NoLower);
 (15%nat,Cut 470 (minus (Times (C 121666) pz) (Times (C 121665) tt)) NoLower);
 (92%nat,Cut 562 (Times det f) FirstPositive);
 (92%nat,Cut 654 (Times g h) NoLower);
 (92%nat,Cut 746 (Times (C sqrt_m1) yy) FirstPositive);
 (43%nat,Cut 789 (Plus iy xx) (FromCarry 765 768 777));
 (15%nat,Cut 804 (minus iy xx) FirstPositive)].
Lemma scheduled_arithmetic : verify input_used plan long O (fun _=>None)=true.
Proof. vm_compute; reflexivity. Qed.
