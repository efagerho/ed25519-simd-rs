From ProofArithmetic Require Import Ranges.
From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.Blocks isa.Instructions execution.WordBounds.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Curve25519 Require Import FieldPolynomial.
From Ed25519Simd Require Import FieldSymbolic.
From Ed25519Simd.CachedAdd Require Import Program CachedAddABI Lane Control Kernels.
Import ListNotations. Open Scope Z_scope.
From Ed25519Simd Require Export FieldTraceBounds.
Definition input_cell affine (a:pointer) :=
 ((Nat.eqb(fst a)point && (snd a<?1280)) ||
  (Nat.eqb(fst a)cached && (snd a<?cache_length affine))) &&
 (0<=?snd a) && (snd a mod 64=?0).
Definition input_limit (a:pointer) :=
 if Nat.eqb (fst a) point then cached_point_limit (Z.to_nat (snd a/64)) else split.
Definition initial_bounds affine : bstate :=
 (fun _=>Range 0(2^64-1),fun a=>Range 0(if input_cell affine a then input_limit a-1 else 2^64-1)).
Definition input_bounds affine s := forall a,input_cell affine a=true ->0<=cells s a<input_limit a.
Lemma initial_bounds_sound affine s : lane_words s ->input_bounds affine s ->bmodels(initial_bounds affine)s.
Proof.
 intros[W M]B;split;intro i;unfold bounded,initial_bounds;cbn [fst snd lower_bound upper_bound].
 - specialize(W i);unfold word64 in *;lia.
 - destruct(input_cell affine i)eqn:E;[specialize(B i E)|specialize(M i)];unfold word64 in *;lia.
Qed.
Theorem bounds_path_checked j full affine : bcheck add_cached_program j (expected_path full affine)(initial_bounds affine)=true.
Proof. destruct full,affine;vm_compute;reflexivity. Qed.
Definition prefix_state j full affine n s := lane_effects j(firstn n(expected_path full affine))s.
Definition prefix_bounds j full affine n := beffects add_cached_program j(firstn n(expected_path full affine))(initial_bounds affine).
Lemma bcheck_prefix j es b n : bcheck add_cached_program j es b=true ->bcheck add_cached_program j(firstn n es)b=true.
Proof. revert es b;induction n;intros[|e es]b H;cbn;auto.
 apply andb_true_iff in H as[E T];rewrite E;apply IHn;exact T. Qed.
Theorem prefix_sound j full affine n s : lane_words s ->input_bounds affine s ->
 bmodels(prefix_bounds j full affine n)(prefix_state j full affine n s).
Proof. intros W B;apply beffects_sound;[apply bcheck_prefix,bounds_path_checked|now apply initial_bounds_sound]. Qed.

Lemma prefix_segment j full affine n m s : (n<=m)%nat ->
 prefix_state j full affine m s=
 lane_effects j(skipn n(firstn m(expected_path full affine)))(prefix_state j full affine n s).
Proof.
 intro N;unfold prefix_state,lane_effects,Machine.execution.Lane.lane_effects.
 rewrite <-(firstn_skipn n(firstn m(expected_path full affine))) at 1.
 rewrite firstn_firstn,Nat.min_l by exact N;apply fold_left_app.
Qed.
