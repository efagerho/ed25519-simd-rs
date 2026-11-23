From Coq Require Import ZArith List Bool Lia.
From Curve25519 Require Import Field Radix51 Edwards.
From Ed25519Simd Require Import Wide51.
Local Open Scope Z_scope.

Definition bounds_for defer c := if (defer && Nat.ltb c 2)%bool then folded_columns else reduced.
Definition point_result defer out (target:nat->coordinates) := forall j c,
  (j<8)%nat -> (c<4)%nat ->
  bounds_for defer c (fun i=>cell out (5*c+i)%nat j) /\
  word_coordinate out j c mod prime=coordinate (target j) c mod prime.
Definition double_spec defer before out := loose_xyz before ->
  point_result defer out (fun j=>double_n 4 (point_values before j)).
Definition addition_spec defer f a before cache out :=
  (f=false ->forall i j,(i<5)%nat ->(j<8)%nat ->cell out (15+i)%nat j=0) /\
  (cached_point_bounds before /\ cache_bounds a cache ->
   point_result defer out (fun j=>add f (point_values before j) (cache_values a cache j))).
Definition point_bounds defer w := forall c j,(c<4)%nat ->(j<8)%nat ->
  bounds_for defer c (fun i=>cell w (5*c+i)%nat j).

Lemma handoff_bounds defer w : point_bounds defer w ->cached_point_bounds w.
Proof.
 intros B r j R J. pose proof(Nat.div_mod r 5 ltac:(lia))as D.
 pose proof(Nat.mod_upper_bound r 5 ltac:(lia))as I.
 specialize (B (r/5)%nat j ltac:(lia) J). unfold bounds_for in B.
 assert(E:(5*(r/5)+r mod 5=r)%nat) by lia.
 unfold cached_point_limit. destruct (Nat.ltb_spec r 10) as [L|L].
 - rewrite (proj2 (Nat.ltb_lt (r/5) 2) ltac:(lia)) in B.
   destruct defer; specialize (B (r mod 5)%nat I);cbv beta in B;rewrite E in B;
    unfold folded_column_bound,output_bound,radix,split in *;destruct (Nat.eqb ((r mod 5) mod 5) 1);lia.
 - rewrite (proj2 (Nat.ltb_ge (r/5) 2) ltac:(lia)), Bool.andb_false_r in B.
   specialize (B (r mod 5)%nat I);cbv beta in B;rewrite E in B.
   unfold output_bound,radix,split in *;destruct (Nat.eqb ((r mod 5) mod 5) 1);lia.
Qed.
Lemma result_values defer w q : point_result defer w q ->point_bounds defer w /\ has_value w q.
Proof. intros H;split;[intros c j C J;apply (proj1 (H j c J C))|].
 intros j J c C;rewrite coord_value by exact C;exact (proj2(H j c J C)). Qed.
Lemma double_values defer w out q : has_value w q ->loose_xyz w ->double_spec defer w out ->
 point_bounds defer out /\ has_value out (fun j=>double_n 4 (q j)).
Proof. intros V B H;destruct(result_values _ _ _ (H B))as [L X];split;[exact L|].
 intros j J c C;etransitivity;[apply X;assumption|apply doubles_equivalent;[apply V,J|exact C]]. Qed.
Lemma add_values defer f a w cache out q : has_value w q ->cached_point_bounds w ->cache_bounds a cache ->
 addition_spec defer f a w cache out ->point_bounds defer out /\ has_value out (fun j=>add f (q j) (cache_values a cache j)).
Proof. intros V B K [_ H];destruct(result_values _ _ _ (H (conj B K)))as [L X];split;[exact L|].
 intros j J c C;etransitivity;[apply X;assumption|apply add_equivalent;[apply V,J|exact C]]. Qed.

Definition agrees_words n (a b:nat->Z) := forall i,(i<n)%nat ->a i=b i.
Lemma double_spec_ext b w o w' o' : agrees_words 160 w' w -> agrees_words 160 o' o ->
 double_spec b w o -> double_spec b w' o'.
Proof. intros W O.
 intros S B j c J C.
   assert (L:loose_xyz w) by (intros h l H L;eapply loose_ext;[|apply (B h l H L)];
     intros i I;unfold cell;apply W;lia).
   destruct(S L j c J C)as[R V];split.
   + unfold bounds_for in *;destruct (_ && _)%bool;intros i I;unfold cell;rewrite O by lia;apply R,I.
   + unfold word_coordinate;rewrite (field_at_ext o' o) by (auto;lia).
     rewrite (point_values_ext w' w) by assumption;exact V.
Qed.
Lemma addition_spec_ext (defer f a:bool) w t o w' t' o' : agrees_words 160 w' w ->
 agrees_words (if a then 120 else 160) t' t -> agrees_words 160 o' o ->
 addition_spec defer f a w t o -> addition_spec defer f a w' t' o'.
Proof. intros W T O.
 intros [Zero S];split.
   + intros F i j I J;unfold cell;rewrite O by lia;apply Zero;assumption.
   + intros [P K] j c J C.
     assert (B:cached_point_bounds w /\ cache_bounds a t).
     { split;intros i l I L;unfold cell;
       [rewrite <-W by lia;apply P;assumption|rewrite <-T by (destruct a;lia);apply K;assumption]. }
     destruct(S B j c J C)as[R V];split.
     * unfold bounds_for in *;destruct (_ && _)%bool;intros i I;unfold cell;rewrite O by lia;apply R,I.
     * unfold word_coordinate;rewrite (field_at_ext o' o) by (auto;lia).
       rewrite (point_values_ext w' w) by assumption.
       rewrite (cache_values_ext _ t' t) by (auto;intros;apply T;destruct a;lia);exact V.
Qed.
