From Coq Require Import List ZArith Lia Ring.
From Curve25519 Require Export Field Radix51 Edwards.
From Ed25519Simd Require Export Wide51.
Import ListNotations. Open Scope Z_scope.

Definition input_bounds (affine:bool) before cached :=
 cached_point_bounds before /\ cache_bounds affine cached.

Definition cached_add_spec full affine before cached after :=
 (full=false ->forall i j,(i<5)%nat ->(j<8)%nat ->cell after(15+i)%nat j=0) /\
 (input_bounds affine before cached ->forall j c,(j<8)%nat ->(c<4)%nat ->
 reduced (fun i=>cell after (5*c+i)%nat j) /\
 word_coordinate after j c mod prime =
 coordinate (add full (point_values before j) (cache_values affine cached j)) c mod prime).
Lemma spec_ext full (affine:bool) before cached after before' cached' after' :
 (forall k,(k<160)%nat ->before' k=before k) ->
 (forall k,(k<(if affine then 120 else 160))%nat ->cached' k=cached k) ->
 (forall k,(k<160)%nat ->after' k=after k) ->
 cached_add_spec full affine before cached after ->cached_add_spec full affine before' cached' after'.
Proof.
 intros In Cache Out[Zero Spec];split.
 - intros F i j I J;unfold cell;rewrite Out by lia;apply Zero;assumption.
 - intros[A B]j c J C.
   assert(Input:input_bounds affine before cached).
   { split;intros i lane I L;unfold cell in *.
     - rewrite <-In by lia;apply A;assumption.
     - rewrite <-Cache by (destruct affine;lia);apply B;assumption. }
   destruct(Spec Input j c J C)as[Bound Value];split.
   + intros i I;unfold cell;rewrite Out by lia;apply Bound;exact I.
   + rewrite (point_values_ext _ _ _ In J), (cache_values_ext _ _ _ _ Cache J).
     unfold word_coordinate;rewrite (field_at_ext after' after) by (auto;lia);exact Value.
Qed.
