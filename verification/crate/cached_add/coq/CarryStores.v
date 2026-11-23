From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.Blocks execution.Lane.
From Curve25519 Require Import Field Radix51 DeferredCarry.
From Ed25519Simd Require Import FieldKernel.
From Ed25519Simd.CachedAdd Require Import Program CachedAddABI KernelInterface CarryHandoff.
Import ListNotations. Local Open Scope Z_scope.

(* The two producers store X with Z and Y with T. Each StoreZmm list
   below is used for both the ELF byte comparison and exec_body. *)
Definition store_field reg disp :=
  map (fun i => StoreZmm (reg+i) 7 (disp+64*Z.of_nat i)) (seq 0 5).
Definition point_stores (yt:bool) :=
  let disp := if yt then 320 else 0 in
  store_field 0%nat disp ++ store_field 5%nat (disp+640).

Definition point_control := Control Caller
  (fun r => if Nat.eqb r 7 then Ptr (point,0) else Unknown) None (fun _ => None).
Definition store_trace yt := exec_body add_cached_program (abi_layout true) point_control (point_stores yt).
Definition transfer_stores yt j regs mem :=
  match store_trace yt with
  | Some (_,es) => cells (lane_effects add_cached_program j es (Lane regs mem))
  | None => mem
  end.

Lemma stores_execute yt : exists es, store_trace yt = Some (point_control, es).
Proof. destruct yt; eexists; reflexivity. Qed.

Definition point_after_products j rx lx ry ly mem :=
  let xz := run lx (paired_product true) rx in
  let yt := run ly (paired_product true) ry in
  transfer_stores true j yt (transfer_stores false j xz mem).

Lemma stored_rows j xz yt mem i : (i<5)%nat ->
  let m := transfer_stores true j yt (transfer_stores false j xz mem) in
  m (point,64*Z.of_nat i) = xz i /\ m (point,320+64*Z.of_nat i) = yt i /\
  m (point,640+64*Z.of_nat i) = xz (5+i)%nat /\
  m (point,960+64*Z.of_nat i) = yt (5+i)%nat.
Proof. intro I; do 5 (destruct i as [|i]; [repeat split; reflexivity|]); lia. Qed.

Definition stored_handoff_semantics j rx lx ry ly consumer mem : Prop :=
  product_inputs rx lx -> product_inputs ry ly ->
  (forall i, WordBounds.word64 (consumer i)) -> operands Kernels.PrepareAB consumer ->
  let m := point_after_products j rx lx ry ly mem in
  let read := lane_load (Lane consumer m) [(7%nat,(point,0))] in
  let out := run read (Kernels.code Kernels.PrepareAB) consumer in
  let xv := product_value rx lx in let yv := product_value ry ly in
  let x i := m (point,64*Z.of_nat i) in
  let y i := m (point,320+64*Z.of_nat i) in
  (forall i, (i<5)%nat -> 0<=sum_columns x y i<2^63 /\
    0<=y i+subtraction_bias i<2^63 /\ 0<=difference_columns x y i<2^63) /\
  (split_field (get out 0) /\ Field.represents (pack out 0) (yv-xv)) /\
  (split_field (get out 5) /\ Field.represents (pack out 5) (yv+xv)) /\
  reduced (fun i => m (point,640+64*Z.of_nat i)) /\
  reduced (fun i => m (point,960+64*Z.of_nat i)).

Local Opaque run paired_product transfer_stores Kernels.code.

Lemma right_bound_at i : (i<5)%nat -> pair_bound true (5+i)%nat = output_bound i.
Proof. intro I; do 5 (destruct i as [|i]; [reflexivity|]); lia. Qed.

Theorem stored_carry_handoff j rx lx ry ly consumer mem :
  stored_handoff_semantics j rx lx ry ly consumer mem.
Proof.
  intros X Y W R m read out xv yv x y.
  pose proof (stored_rows j (run lx (paired_product true) rx)
    (run ly (paired_product true) ry) mem) as Rows.
  assert (Loaded : forall i, (i<5)%nat ->
    read 7%nat (64*Z.of_nat i) = left_result rx lx i /\
    read 7%nat (320+64*Z.of_nat i) = left_result ry ly i).
  { intros i I; destruct (Rows i I) as [A [B _]]; split; [exact A|exact B]. }
  destruct (assembly_carry_handoff _ _ _ _ _ _ X Y W R Loaded) as [Bounds [D S]].
  split.
  { intros i I. specialize (Bounds i I).
    destruct (Loaded i I) as [A B].
    change (x i = left_result rx lx i) in A.
    change (y i = left_result ry ly i) in B.
    unfold sum_columns, difference_columns in *; now rewrite A,B. }
  split; [exact D|]. split; [exact S|].
  destruct X as [WX [RX MX]], Y as [WY [RY MY]].
  destruct (paired_product_correct true rx lx WX RX MX 5%nat (or_intror (or_introl eq_refl))) as [Zb _].
  destruct (paired_product_correct true ry ly WY RY MY 5%nat (or_intror (or_introl eq_refl))) as [Tb _].
  split; intros i I; destruct (Rows i I) as [_ [_ [Zrow Trow]]]; unfold m,point_after_products.
  - rewrite Zrow, <- (right_bound_at i I); apply (Zb i I).
  - rewrite Trow, <- (right_bound_at i I); apply (Tb i I).
Qed.
