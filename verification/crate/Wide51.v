From Coq Require Import List ZArith Lia Ring.
From Machine Require Import memory.VectorBuffer.
From Curve25519 Require Import Field Radix51 Edwards.
Import ListNotations. Open Scope Z_scope.

Definition cell (buf:nat -> Z) (i lane:nat) := buf (i*8+lane)%nat.
Lemma cell_words_at m region i j : (j<8)%nat ->
 cell (words_at m region) i j = m (vector_address region 0 i) j.
Proof. apply words_at_lane. Qed.

Definition field_at buf start lane := limbs (fun i=>cell buf (start+i)%nat lane).

Definition word_coordinate words lane c := field_at words (5*c)%nat lane.
Definition point_from_fields (f:nat->Z) := Coordinates (f 0%nat) (f 1%nat) (f 2%nat) (f 3%nat).
Definition cache_from_fields (affine:bool) (f:nat->Z) :=
 CachedCoordinates (f 0%nat) (f 1%nat) (f 2%nat) (if affine then None else Some (f 3%nat)).
(* A scalar table row stores each field as five consecutive qwords. *)
Definition scalar_cache affine (row:nat->Z) :=
 cache_from_fields affine (fun c=>limbs (fun i=>row (5*c+i)%nat)).
Definition point_values words lane := point_from_fields (word_coordinate words lane).
Definition cache_values affine words lane := cache_from_fields affine (word_coordinate words lane).

Definition loose_xyz words := forall c j, (c<3)%nat -> (j<8)%nat ->
 loose (fun i => cell words (5*c+i)%nat j).

Definition has_value words value := forall j,(j<8)%nat ->
 equivalent (point_values words j) (value j).
Definition strict words := forall c j,(c<4)%nat -> (j<8)%nat ->
 reduced (fun i=>cell words (5*c+i)%nat j).
Definition cache_bounds (affine:bool) w := forall i j,
 (i<(if affine then 15 else 20))%nat -> (j<8)%nat ->
 0<=cell w i j<2^52.

Lemma coord_value w j c : (c<4)%nat ->
 coordinate (point_values w j) c=word_coordinate w j c.
Proof. destruct c as [|[|[|[|c]]]];try reflexivity;lia. Qed.
Lemma strict_loose w : strict w -> loose_xyz w.
Proof. intros H c j C J;apply reduced_loose,H;lia. Qed.
Lemma strict_split w : strict w -> cache_bounds false w.
Proof.
 intros H i j I J;change (i<20)%nat in I.
 pose proof(Nat.div_mod i 5 ltac:(lia));pose proof(Nat.mod_upper_bound i 5 ltac:(lia));
 assert (Ci:(i/5 < 4)%nat) by lia;assert (Mi:(i mod 5 < 5)%nat) by lia;specialize(H (i/5)%nat j Ci J (i mod 5)%nat Mi).
 cbv beta in H;rewrite <-H0 in H.
 unfold output_bound in H;destruct (Nat.eqb ((i mod 5) mod 5) 1) in H;
 unfold radix,split in *;lia.
Qed.
Lemma field_at_ext a b start j :
 (forall k,(k<160)%nat ->a k=b k) ->(start+5<=20)%nat ->(j<8)%nat ->field_at a start j=field_at b start j.
Proof. intros E S J;unfold field_at,limbs,cell;repeat rewrite E by lia;reflexivity. Qed.
Lemma point_values_ext a b j :
 (forall k,(k<160)%nat ->a k=b k) ->(j<8)%nat ->point_values a j=point_values b j.
Proof. intros E J;unfold point_values,point_from_fields,word_coordinate;repeat rewrite(field_at_ext a b)by (auto;lia);reflexivity. Qed.
Lemma cache_values_ext (affine:bool) a b j :
 (forall k,(k<(if affine then 120 else 160))%nat -> a k=b k) -> (j<8)%nat ->
 cache_values affine a j=cache_values affine b j.
Proof.
 intros E J;unfold cache_values,cache_from_fields,word_coordinate,field_at,limbs,cell;
 destruct affine;repeat rewrite E by lia;reflexivity.
Qed.
