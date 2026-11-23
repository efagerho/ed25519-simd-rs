From Coq Require Import List ZArith Lia.
From Machine Require Import execution.Blocks execution.Lane execution.LaneTrace execution.TraceEquivalence.
From Ed25519Simd Require Import PointFrame.
From Ed25519Simd.Double4 Require Program Round.
From Ed25519Simd.CachedAdd Require Program Control Kernels.
From Ed25519Simd.Point Require Import Double DoublePath Add AddPath.
Import ListNotations. Local Open Scope Z_scope.

Definition point_row n : pointer := (point,64 * Z.of_nat n).
Definition output_rows := map point_row (seq 0 20).
Definition row c i := point_row (5*c+i).
Definition carry_at c :=
  [Constant 28 19;Constant 29 (2^51-1)] ++
  map (fun i=>LoadCell i (row c i)) (seq 0 5) ++
  map (vector_action []) (Kernels.code Kernels.CarryY) ++
  map (fun i=>StoreCell i (row c i)) (seq 0 5).
Definition finish (defer:bool) := if defer then carry_at 0 ++ carry_at 1 else [].
Definition double_trace priv := trace Double.program (double_effects priv) ++ finish priv.
Definition reference_double := trace Double4.Program.double4_program Round.expected_path.
Definition add_trace m := trace Add.program (add_effects m) ++ finish (deferred m).
Definition reference_add m := trace CachedAdd.Program.add_cached_program
  (Control.expected_path (full m) (affine m)).
Definition same_outputs x y := check (circuit_for x y) x y output_rows.
Lemma double_outputs_checked priv : same_outputs (double_trace priv) reference_double=true.
Proof. destruct priv; vm_compute; reflexivity. Qed.
Lemma add_outputs_checked m : same_outputs (add_trace m) (reference_add m)=true.
Proof. destruct m as [[] []|]; vm_compute; reflexivity. Qed.

Definition normalized defer j s := fold_left (perform j) (finish defer) s.
Lemma rows_correct p es q fs defer j s :
  same_outputs (trace p es ++ finish defer) (trace q fs)=true ->
  forall n,(n<20)%nat ->
  cells (normalized defer j (lane_effects p j es s)) (point_row n) =
  cells (lane_effects q j fs s) (point_row n).
Proof.
  intros H n N. pose proof (check_sound j s _ _ _ _ H (point_row n)) as E.
  rewrite fold_left_app,!trace_exact in E. apply E, in_map, in_seq; lia.
Qed.
Theorem double_rows priv j s : forall n,(n<20)%nat ->
  cells (normalized priv j (lane_effects Double.program j (double_effects priv) s)) (point_row n) =
  cells (lane_effects Double4.Program.double4_program j Round.expected_path s) (point_row n).
Proof. apply rows_correct, double_outputs_checked. Qed.
Theorem add_rows m j s : forall n,(n<20)%nat ->
  cells (normalized (deferred m) j (lane_effects Add.program j (add_effects m) s)) (point_row n) =
  cells (lane_effects CachedAdd.Program.add_cached_program j (Control.expected_path (full m) (affine m)) s)
    (point_row n).
Proof. apply rows_correct, add_outputs_checked. Qed.
