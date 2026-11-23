From Coq Require Import List ZArith Bool Lia.
From ProofArithmetic Require Import Interval.
From Machine Require Import isa.Instructions execution.WordBounds.
From Curve25519 Require Import Field Radix51 DeferredCarry FieldPolynomial.
From Ed25519Simd Require Import FieldKernel FieldSymbolic.
From Ed25519Simd.CachedAdd Require Import Kernels KernelInterface KernelCalls.
Import ListNotations. Local Open Scope Z_scope.

(* The shared pair kernel takes two fields in ZMM0..4 and ZMM5..9 and
   multiplies both by the same field at R8. Isolate its right product
   after the five loads, left folded product, and fifteen carries. *)
Definition folded_product := code Single.
Definition normalize_left := firstn 15 (code CarryY).
Definition right_product := skipn (length folded_product + length normalize_left) (code Pair).
Definition paired_product (defer:bool) :=
  folded_product ++ (if defer then [] else normalize_left) ++ right_product.
Definition pair_bound (defer:bool) reg :=
  if defer && Nat.ltb reg 5 then folded_column_bound else output_bound reg.

Lemma ordinary_pair_is_carried : code Pair = paired_product false.
Proof. vm_compute; reflexivity. Qed.

Lemma pair_checked defer :
  FieldKernel.check_kernel (paired_product defer) (initial Pair) (hints Pair)
    (loads Pair) (output_starts Pair) (pair_bound defer) (target Pair) = true.
Proof. destruct defer; vm_compute; reflexivity. Qed.

(* This is a statement about executing the instructions. The other product
   (Z or T) retains the usual output bounds on both paths. *)
Definition pair_semantics defer r load : Prop :=
  (forall i, word64 (r i)) -> operands Pair r ->
  let m := fun i => load 8%nat (64*Z.of_nat i) in
  split_field m ->
  forall start, In start [0%nat;5%nat] ->
  let out := run load (paired_product defer) r in
  field_bound (fun i => pair_bound defer (start+i)%nat) (get out start) /\
  represents (pack out start) (pack r start * limbs m).

Theorem paired_product_correct defer r load : pair_semantics defer r load.
Proof.
  intros W Reg m Mem start S out.
  assert (L : loads_of (paired_product defer) = loads_of (code Pair)).
  { destruct defer; vm_compute; reflexivity. }
  pose proof (initial_models Pair r m W Reg) as Init.
  assert (Read : forall b d, In (b,d) (loads_of (paired_product defer)) ->
    models (env r m) (loads Pair b d) (load b d)).
  { rewrite L. apply loads_models; [intros i I; apply Mem, I|reflexivity]. }
  destruct (FieldKernel.kernel_correct _ _ _ _ _ _ _ (pair_checked defer)
    (env r m) load r (proj1 (proj2 (proj2 Reg))) (valid_hints _ _ _ W Reg)
    Read Init start S) as [B V].
  split; [exact B|]. rewrite target_value_ok in V; exact V.
Qed.

Definition rhs_field (load:nat -> Z -> Z) i := load 8%nat (64*Z.of_nat i).
Definition product_inputs r load :=
  (forall i, word64 (r i)) /\ operands Pair r /\ split_field (rhs_field load).
Definition product_value r load := pack r 0 * limbs (rhs_field load).
Definition left_result r load := get (run load (paired_product true) r) 0.

Local Opaque paired_product code run.

Lemma left_result_correct r load : product_inputs r load ->
  folded_columns (left_result r load) /\
  represents (limbs (left_result r load)) (product_value r load).
Proof.
  intros [W [R M]]. destruct (paired_product_correct true r load W R M 0%nat (or_introl eq_refl)) as [B V].
  split; [|exact V]. intros i I; specialize (B i I).
  unfold pair_bound in B; cbn [andb Nat.add] in B.
  now rewrite (proj2 (Nat.ltb_lt _ _) I) in B.
Qed.

Local Opaque left_result product_value.

Definition handoff_semantics rx lx ry ly consumer read : Prop :=
  product_inputs rx lx -> product_inputs ry ly ->
  (forall i, word64 (consumer i)) -> operands PrepareAB consumer ->
  let x := left_result rx lx in let y := left_result ry ly in
  (forall i, (i<5)%nat ->
    read 7%nat (64*Z.of_nat i)=x i /\
    read 7%nat (320+64*Z.of_nat i)=y i) ->
  let regs := run read (code PrepareAB) consumer in
  let xv := product_value rx lx in let yv := product_value ry ly in
  (forall i, (i<5)%nat -> 0<=sum_columns x y i<2^63 /\
     0<=y i+subtraction_bias i<2^63 /\ 0<=difference_columns x y i<2^63) /\
  (split_field (get regs 0) /\ represents (pack regs 0) (yv-xv)) /\
  (split_field (get regs 5) /\ represents (pack regs 5) (yv+xv)).

Theorem assembly_carry_handoff rx lx ry ly consumer read : handoff_semantics rx lx ry ly consumer read.
Proof.
  intros X Y W Input x y Loaded regs xv yv.
  destruct (left_result_correct _ _ X) as [XB XV].
  destruct (left_result_correct _ _ Y) as [YB YV].
  change (folded_columns x) in XB; change (represents (limbs x) xv) in XV.
  change (folded_columns y) in YB; change (represents (limbs y) yv) in YV.
  split; [exact (proj1 (deferred_carry_correct x y XB YB))|].
  set (m := fun i => read 7%nat (64*Z.of_nat i)).
  assert (LX : forall i,(i<5)%nat -> m i=x i) by (intros i I;exact (proj1 (Loaded i I))).
  assert (LY : forall i,(i<5)%nat -> m (5+i)%nat=y i).
  { intros i I;unfold m;rewrite Nat2Z.inj_add;replace (64*(Z.of_nat 5+Z.of_nat i))
      with (320+64*Z.of_nat i) by (change (Z.of_nat 5) with 5;ring).
    exact (proj2 (Loaded i I)). }
  assert (Right : right_ok PrepareAB m).
  { intros i I; change (i<10)%nat in I. destruct (Nat.lt_ge_cases i 5) as [L|L].
    - rewrite LX by exact L; apply XB,L.
    - replace i with (5+(i-5))%nat by lia. rewrite LY by lia;apply YB;lia. }
  pose proof (run_correct PrepareAB consumer read m 0 W Input Right
    ltac:(intros;reflexivity) (or_introl eq_refl)) as [DB DV].
  pose proof (run_correct PrepareAB consumer read m 5 W Input Right
    ltac:(intros;reflexivity) (or_intror (or_introl eq_refl))) as [SB SV].
  rewrite target_value_ok in DV,SV. change (represents (pack regs 0) (pack m 5-pack m 0)) in DV.
  change (represents (pack regs 5) (pack m 5+pack m 0)) in SV.
  assert (PX:pack m 0=limbs x) by (apply limbs_ext;exact LX).
  assert (PY:pack m 5=limbs y) by (apply limbs_ext;exact LY).
  rewrite PX,PY in DV,SV.
  split;split;[exact DB|eapply ctrans;[exact DV|apply cminus;assumption]|
               exact SB|eapply ctrans;[exact SV|apply cplus;assumption]].
Qed.

(* An affine caller may also put 2Z in ZMM22..26 and jump into the
   second half of the independent-products kernel. The return then enters
   the ordinary F/G block with D and the folded C in registers. *)
Definition twice_z :=
  map (fun i => ((22+i)%nat,Load 7 (640+64*Z.of_nat i))) (seq 0 5) ++
  map (fun i => ((22+i)%nat,Add (22+i) (22+i))) (seq 0 5).
Definition affine_tail := skipn (length folded_product) (code Independent).
Definition affine_fg := twice_z ++ affine_tail ++ code PrepareFG.
Definition affine_initial i :=
  if Nat.eqb i 30 || Nat.eqb i 31 then initial PrepareFG i else initial Single i.
Definition affine_target start :=
  let d := Times (C 2) (packE memvar 10) in
  let c := Times (packE regvar 0) (packE memvar 0) in
  if Nat.eqb start 0 then minus d c else Plus d c.

Lemma affine_checked :
  FieldKernel.check_kernel affine_fg affine_initial [] (loads Single)
    [0%nat;10%nat] (fun _ => split-1) affine_target = true.
Proof. vm_compute; reflexivity. Qed.

Definition affine_operands r read :=
  (forall i, word64 (r i)) /\ operands Single r /\
  r 30%nat=bias 0 /\ r 31%nat=bias 1 /\ split_field (rhs_field read) /\
  split_field (fun i => read 7%nat (640+64*Z.of_nat i)).

Definition affine_semantics r read : Prop := affine_operands r read ->
  let d := 2 * limbs (fun i => read 7%nat (640+64*Z.of_nat i)) in
  let c := pack r 0 * limbs (rhs_field read) in
  let out := run read affine_fg r in
  (split_field (get out 0) /\ represents (pack out 0) (d-c)) /\
  (split_field (get out 10) /\ represents (pack out 10) (d+c)).

Theorem affine_carry_handoff r read : affine_semantics r read.
Proof.
  intros [W [R [B0 [B1 [Right Zb]]]]] d c out.
  set (m := fun i => if Nat.ltb i 5 then rhs_field read i else read 7%nat (64*Z.of_nat i)).
  assert (Init : forall i, models (env r m) (affine_initial i) (r i)).
  { intro i; unfold affine_initial. destruct (_ || _)%bool eqn:E.
    - apply orb_true_iff in E. destruct E as [E|E];apply Nat.eqb_eq in E;subst i;
        rewrite ?B0,?B1. all: split; [reflexivity|split; apply Z.le_refl].
    - apply initial_models;assumption. }
  assert (L : forall b off, In (b,off) (loads_of affine_fg) ->
    models (env r m) (loads Single b off) (read b off)).
  { intros b off H.
    change (In (b,off) [(7%nat,640);(7%nat,704);(7%nat,768);(7%nat,832);(7%nat,896);
                        (8%nat,0);(8%nat,64);(8%nat,128);(8%nat,192);(8%nat,256)]) in H.
    cbn [In] in H. repeat destruct H as [H|H];try contradiction;
      inversion H;subst;clear H;unfold models,loads;cbn [term lower upper I enclosure lower_bound upper_bound];
      rewrite env_mem. all: split; [reflexivity|].
    all: first [exact (Zb 0%nat ltac:(lia)) | exact (Zb 1%nat ltac:(lia)) |
                exact (Zb 2%nat ltac:(lia)) | exact (Zb 3%nat ltac:(lia)) |
                exact (Zb 4%nat ltac:(lia)) | exact (Right 0%nat ltac:(lia)) |
                exact (Right 1%nat ltac:(lia)) | exact (Right 2%nat ltac:(lia)) |
                exact (Right 3%nat ltac:(lia)) | exact (Right 4%nat ltac:(lia))]. }
  pose proof (FieldKernel.kernel_correct _ _ _ _ _ _ _ affine_checked (env r m) read r
    (proj1 (proj2 (proj2 R))) (Forall_nil _) L Init) as K.
  destruct (K 0%nat (or_introl eq_refl)) as [FB F].
  destruct (K 10%nat (or_intror (or_introl eq_refl))) as [GB G].
  cbn [affine_target Nat.eqb minus val] in F,G.
  rewrite !pack_env_mem,!pack_env_reg in F,G.
  split;split;[exact FB|exact F|exact GB|exact G].
Qed.
