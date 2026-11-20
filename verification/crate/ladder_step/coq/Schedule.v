From Coq Require Import List ZArith Znumtheory Lia.
From Ed25519Simd Require Export Wide51.
From Curve25519 Require Import Field Edwards.
From Ed25519Simd.Double4 Require Import Double4Spec.
From Ed25519Simd.CachedAdd Require CachedAddSpec.
Open Scope Z_scope.

Definition ladder_formula full q odd base even :=
 let first := add false (double_n 4 q) odd in
 let second := add true (double_n 4 first) base in
 add full second even.

Lemma double_result w out q : has_value w q -> loose_xyz w ->
 double4_spec w out -> strict out /\ has_value out (fun j=>double_n 4 (q j)).
Proof.
 intros V B S;split;[intros c j C J;exact(proj1(S B j c J C))|].
 intros j J c C;rewrite coord_value by exact C.
 etransitivity;[exact(proj2(S B j c J C))|].
 apply doubles_equivalent;[apply V;exact J|exact C].
Qed.
Lemma add_result full affine w cached out q :
 has_value w q -> strict w -> cache_bounds affine cached ->
 CachedAddSpec.cached_add_spec full affine w cached out ->
 strict out /\ has_value out (fun j=>add full (q j) (cache_values affine cached j)).
Proof.
 intros V B K [_ S];specialize(S (conj (strict_split w B) K));split.
 - intros c j C J;exact(proj1(S j c J C)).
 - intros j J c C;rewrite coord_value by exact C;etransitivity.
   + exact(proj2(S j c J C)).
   + apply add_equivalent;[apply V;exact J|exact C].
Qed.
