From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordBounds execution.Lane execution.LaneTrace.
From Curve25519 Require Import Field Radix51 FieldPolynomial.
From Ed25519Simd Require Import FieldKernel FieldSymbolic.
From Ed25519Simd.CachedAdd Require Import Kernels KernelInterface.
From Ed25519Simd.Point Require Import Outputs.
Import ListNotations. Local Open Scope Z_scope.

Local Opaque code run.

Definition field c s := fun i=>cells s (row c i).
Definition load_field c j s := fold_left (perform j)
  ([Constant 28 19;Constant 29 (2^51-1)] ++ map (fun i=>LoadCell i (row c i)) (seq 0 5)) s.
Definition save_field c j s := fold_left (perform j)
  (map (fun i=>StoreCell i (row c i)) (seq 0 5)) s.
Definition carried c j s := fold_left (perform j) (carry_at c) s.
Definition result c j s := run (fun _ _=>0) (code CarryY) (registers (load_field c j s)).
Lemma carry_eval c j s :
  carried c j s = save_field c j (Lane (result c j s) (cells s)).
Proof.
  unfold carried,carry_at,save_field,result. generalize (code CarryY); intro instructions. rewrite !fold_left_app.
  destruct s as [rs m]; cbn [map seq fold_left perform registers cells]. rewrite vectors_exact. reflexivity.
Qed.
Lemma loaded_limbs c j s i : (i<5)%nat -> registers (load_field c j s) i=field c s i.
Proof. do 5 (destruct i as [|i]; [reflexivity|]);lia. Qed.
Lemma loaded_words c j s : lane_words s -> forall r, word64 (registers (load_field c j s) r).
Proof.
  intros [R M] r. cbv [load_field fold_left map seq app perform registers cells put].
  repeat destruct (Nat.eqb _ r); auto; unfold word64; lia.
Qed.
Lemma saved_words c j r m : (forall k,word64(r k)) -> (forall a,word64(m a)) ->
  lane_words (save_field c j (Lane r m)).
Proof.
  intros R M; split;[exact R|]. intro a;cbv [save_field fold_left map seq app perform registers cells].
  repeat destruct (Blocks.ptr_eq a _);auto.
Qed.
Lemma carry_words c j s : lane_words s -> lane_words (carried c j s).
Proof. intro W;rewrite carry_eval;apply saved_words;[|apply W].
  apply run_words;[intros;unfold word64;lia|now apply loaded_words]. Qed.

Lemma saved_same c j r m i : (c<2)%nat -> (i<5)%nat ->
  field c (save_field c j (Lane r m)) i=r i.
Proof. intros C I;do 2 (destruct c as [|c];[do 5 (destruct i as [|i];[reflexivity|]);lia|]);lia. Qed.
Lemma saved_other c d j r m i : (c<2)%nat -> (d<4)%nat -> c<>d -> (i<5)%nat ->
  field d (save_field c j (Lane r m)) i=m (row d i).
Proof.
  intros C D N I;do 2 (destruct c as [|c];[do 4 (destruct d as [|d];
    [try congruence;do 5 (destruct i as [|i];[reflexivity|]);lia|]);lia|]);lia.
Qed.
Lemma carry_other c d j s i : (c<2)%nat -> (d<4)%nat -> c<>d -> (i<5)%nat ->
  field d (carried c j s) i=field d s i.
Proof. intros;rewrite carry_eval;now apply saved_other. Qed.
Lemma carry_value c j s : (c<2)%nat ->lane_words s -> folded_columns (field c s) ->
  represents (limbs (field c (carried c j s))) (limbs (field c s)).
Proof.
  intros C W F. set (r:=registers (load_field c j s)).
  assert (R:forall i,word64(r i)) by now apply loaded_words.
  assert (Ops:operands CarryY r).
  { split;[|repeat split;try reflexivity;discriminate].
    intros i I;unfold input_bound;rewrite (proj2 (Nat.ltb_lt _ _) I).
    destruct (Nat.ltb_spec i 5) as [L|G].
    - unfold r;rewrite loaded_limbs by exact L;now apply F.
    - specialize (R i);unfold word64 in R;lia. }
  pose proof (run_correct CarryY r (fun _ _=>0) (fun _=>0) 0 R Ops
    ltac:(intros i H;inversion H) ltac:(reflexivity) (or_introl eq_refl)) as [_ V].
  change (represents (pack (result c j s) 0) (val (env r (fun _=>0)) (packE regvar 0))) in V.
  rewrite pack_env_reg in V. rewrite carry_eval.
  replace (limbs (field c (save_field c j (Lane (result c j s) (cells s)))))
    with (pack (result c j s) 0) by (symmetry;apply limbs_ext;intros;now apply saved_same).
  replace (limbs (field c s)) with (pack r 0) by (apply limbs_ext;intros;now apply loaded_limbs).
  exact V.
Qed.

Definition raw_bounds s := forall c,(c<2)%nat -> folded_columns (field c s).
Lemma finish_other defer c j s i : (c<4)%nat -> (i<5)%nat ->
  (defer=false \/ (2<=c)%nat) -> field c (normalized defer j s) i=field c s i.
Proof.
  intros C I [->|L];[reflexivity|]. destruct defer;[|reflexivity].
  unfold normalized,finish;rewrite fold_left_app.
  change (field c (carried 1 j (carried 0 j s)) i=field c s i).
  rewrite !carry_other by lia;reflexivity.
Qed.
Theorem finish_value defer c j s : (c<4)%nat -> lane_words s ->
  (defer=true ->raw_bounds s) ->
  represents (limbs (field c (normalized defer j s))) (limbs (field c s)).
Proof.
  intros C W B. destruct defer;[|apply crefl]. specialize (B eq_refl).
  unfold normalized,finish;rewrite fold_left_app.
  change (represents (limbs (field c (carried 1 j (carried 0 j s)))) (limbs (field c s))).
  assert (E:forall d,(d<4)%nat -> d<>0%nat -> forall i,(i<5)%nat ->
    field d (carried 0 j s) i=field d s i) by (intros;apply carry_other;lia).
  destruct c as [|[|c]].
  - rewrite (limbs_ext _ (field 0 (carried 0 j s))) by (intros;apply carry_other;lia).
    apply carry_value;[lia|exact W|apply B;lia].
  - rewrite <- (limbs_ext _ _ (E 1%nat ltac:(lia) ltac:(lia))).
    apply carry_value;[lia|now apply carry_words|]. eapply field_bound_ext;[|apply (B 1%nat);lia].
    intros;symmetry;apply E;lia.
  - replace (limbs (field (S(S c)) (carried 1 j (carried 0 j s)))) with (limbs (field (S(S c)) s));[apply crefl|symmetry;apply limbs_ext].
    intros;rewrite !carry_other by lia;reflexivity.
Qed.
