From Coq Require Import List ZArith Lia Ring.
Require Import FieldSpec.
Require Export Bounds.
Import ListNotations. Open Scope Z_scope.
(* Coordinates are integers interpreted modulo p. No curve membership or
   relation involving the incoming T coordinate is a precondition. *)
Record coordinates := Coordinates { cx : Z; cy : Z; cz : Z; ct : Z }.
Definition doubling q :=
 let a := cx q * cx q in
 let b := cy q * cy q in
 let c := cz q * cz q in
 let d := (cx q + cy q) * (cx q + cy q) in
 let e := d - a - b in
 let g := b - a in
 let f := g - 2*c in
 let h := -a - b in
 Coordinates (e*f) (g*h) (f*g) (e*h).
Fixpoint double_n n q :=
 match n with O => q | S n => doubling (double_n n q) end.
Definition coordinate q n :=
 match n with 0%nat => cx q | 1%nat => cy q | 2%nat => cz q | _ => ct q end.
Definition point_values words lane := Coordinates
 (field_at words 0 lane) (field_at words 5 lane) (field_at words 10 lane) (field_at words 15 lane).
Definition input_bounds words := forall c j, (c<3)%nat -> (j<8)%nat ->
 loose (fun i => cell words (5*c+i)%nat j).

(* The arithmetic guarantee is conditional on the three coordinate bounds.
   The public theorem separately guarantees memory/ABI safety for any qwords. *)
Definition double4_spec before after := input_bounds before ->
 forall j c, (j<8)%nat -> (c<4)%nat ->
 reduced (fun i => cell after (5*c+i)%nat j) /\
 field_at after (5*c)%nat j mod prime =
 coordinate (double_n 4 (point_values before j)) c mod prime.
Lemma represents_mod x y : represents x y -> x mod prime=y mod prime.
Proof. intros[k E];rewrite E,Z.add_mod,Z.mul_mod;[|unfold prime;lia|unfold prime;lia].
 rewrite Z.mod_same,Z.mul_0_r,Z.mod_0_l,Z.add_0_r,Z.mod_mod by (unfold prime;lia);reflexivity.
Qed.
Lemma cminus x y u v : represents x y -> represents u v -> represents (x-u)(y-v).
Proof. intros[a A][b B];exists(a-b);rewrite A,B;ring. Qed.
Lemma cneg x y : represents x y -> represents(-x)(-y).
Proof. intros[k E];exists(-k);rewrite E;ring. Qed.
Lemma field_at_ext a b start j :
 (forall k,(k<160)%nat ->a k=b k) ->(start+5<=20)%nat ->(j<8)%nat ->field_at a start j=field_at b start j.
Proof. intros E S J;unfold field_at,limbs,cell;repeat rewrite E by lia;reflexivity. Qed.
Lemma point_values_ext a b j :
 (forall k,(k<160)%nat ->a k=b k) ->(j<8)%nat ->point_values a j=point_values b j.
Proof. intros E J;unfold point_values;repeat rewrite(field_at_ext a b)by (auto;lia);reflexivity. Qed.
Lemma spec_ext before after before' after' :
 (forall k,(k<160)%nat ->before' k=before k) ->
 (forall k,(k<160)%nat ->after' k=after k) ->
 double4_spec before after -> double4_spec before' after'.
Proof.
 intros In Out Spec Bound j c J C.
 assert(B:input_bounds before).
 { intros coord lane CI LI;apply(loose_ext (fun i=>cell before'(5*coord+i)%nat lane));[|apply Bound;assumption].
   intros i I;unfold cell;apply In;lia. }
 destruct(Spec B j c J C)as[Bounds V];split.
 - intros i I;unfold cell;rewrite Out by lia;apply Bounds;exact I.
 - rewrite(field_at_ext after' after)by (auto;lia);rewrite(point_values_ext before' before)by (auto;lia);exact V.
Qed.
