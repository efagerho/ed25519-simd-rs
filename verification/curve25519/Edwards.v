From Coq Require Import List ZArith Znumtheory Lia Ring.
From Curve25519 Require Import Field.
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
Record cached_coordinates := CachedCoordinates {
  y_minus_x : Z; y_plus_x : Z; t2d : Z; doubled_z : option Z
}.

Definition add (full : bool) (p : coordinates) (q : cached_coordinates) :=
 let a := (cy p - cx p) * y_minus_x q in
 let b := (cy p + cx p) * y_plus_x q in
 let c := ct p * t2d q in
 let d := match doubled_z q with None => 2 * cz p | Some zz => cz p * zz end in
 let e := b-a in let f := d-c in let g := d+c in let h := b+a in
 Coordinates (e*f) (g*h) (f*g) (if full then e*h else 0).

Definition equivalent (p q:coordinates) :=
 forall c,(c<4)%nat -> eqm prime (coordinate p c) (coordinate q c).
Local Ltac congruent :=
 first [apply Zplus_eqm;congruent |apply Zminus_eqm;congruent|
        apply Zmult_eqm;congruent|apply Zopp_eqm;congruent|
        apply eqm_refl|assumption].
Lemma doubling_equivalent p q : equivalent p q -> equivalent(doubling p)(doubling q).
Proof.
 intros E;pose proof(E 0%nat ltac:(lia)) as X;pose proof(E 1%nat ltac:(lia)) as Y;
 pose proof(E 2%nat ltac:(lia)) as Zc.
 cbn [coordinate] in X,Y,Zc;intros [|[|[|c]]] _;cbn [coordinate doubling];congruent.
Qed.
Lemma doubles_equivalent n p q : equivalent p q -> equivalent(double_n n p)(double_n n q).
Proof. intro E;induction n;[exact E|now apply doubling_equivalent]. Qed.
Lemma add_equivalent full p q cache :
 equivalent p q -> equivalent (add full p cache) (add full q cache).
Proof.
 intros E;pose proof(E 0%nat ltac:(lia));pose proof(E 1%nat ltac:(lia));
 pose proof(E 2%nat ltac:(lia));pose proof(E 3%nat ltac:(lia)).
 cbn [coordinate] in *;destruct cache as [ym yp td [zz|]], full;
 intros [|[|[|c]]] _;cbn [coordinate add cx cy cz ct y_minus_x y_plus_x t2d doubled_z];congruent.
Qed.
