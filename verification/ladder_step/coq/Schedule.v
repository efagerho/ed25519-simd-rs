From Coq Require Import List ZArith Znumtheory RelationClasses Lia.
From Machine Require Import ByteMemory.
From Double4 Require Import Double4Spec.
From CachedAdd Require CachedAddSpec.
Import ListNotations. Open Scope Z_scope.

Definition prime := Double4.FieldSpec.prime.
Definition coords := Double4Spec.coordinates.
Definition pack (f:nat->Z) := Coordinates (f 0%nat) (f 1%nat) (f 2%nat) (f 3%nat).
Definition add (full affine:bool) q cache :=
 pack (CachedAddSpec.addition full affine (coordinate q) cache).
Definition cached_at m a j := CachedAddSpec.coordinate (buffer_words m a) j.
Definition ladder_formula full q odd base even :=
 let first := add false false (double_n 4 q) odd in
 let second := add true true (double_n 4 first) base in
 add full false second even.

Definition equivalent (p q:coords) :=
 forall c,(c<4)%nat -> eqm prime (coordinate p c) (coordinate q c).
Definition has_value words value := forall j,(j<8)%nat ->
 equivalent (point_values words j) (value j).
Definition strict words := forall c j,(c<4)%nat -> (j<8)%nat ->
 Double4.Bounds.reduced (fun i=>Double4.FieldSpec.cell words (5*c+i)%nat j).
Definition cache_bounds (affine:bool) w := forall i j,
 (i<(if affine then 15 else 20))%nat -> (j<8)%nat ->
 0<=Double4.FieldSpec.cell w i j<2^52.

Lemma coord_value w j c : (c<4)%nat ->
 coordinate (point_values w j) c=CachedAddSpec.coordinate w j c.
Proof. destruct c as [|[|[|[|c]]]];try reflexivity;lia. Qed.
Lemma coord_pack f c : (c<4)%nat -> coordinate(pack f)c=f c.
Proof. destruct c as [|[|[|[|c]]]];try reflexivity;lia. Qed.
Lemma strict_loose w : strict w -> input_bounds w.
Proof. intros H c j C J;apply Double4.Bounds.reduced_loose,H;lia. Qed.
Lemma strict_split w : strict w -> cache_bounds false w.
Proof.
 intros H i j I J;change (i<20)%nat in I.
 pose proof(Nat.div_mod i 5 ltac:(lia));pose proof(Nat.mod_upper_bound i 5 ltac:(lia));
 assert (Ci:(i/5 < 4)%nat) by lia;assert (Mi:(i mod 5 < 5)%nat) by lia;specialize(H (i/5)%nat j Ci J (i mod 5)%nat Mi).
 cbv beta in H;rewrite <-H0 in H.
 unfold Double4.Bounds.output_bound in H;destruct (Nat.eqb ((i mod 5) mod 5) 1) in H;
 unfold Double4.FieldSpec.radix,Double4.FieldSpec.split in *;lia.
Qed.
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
Lemma add_equivalent (full affine:bool) p q a b :
 equivalent p q -> (forall c,(c<(if affine then 3 else 4))%nat -> eqm prime (a c)(b c)) ->
 equivalent(add full affine p a)(add full affine q b).
Proof.
 intros E K c C;unfold add;rewrite !coord_pack by exact C.
 pose proof(E 0%nat ltac:(lia));pose proof(E 1%nat ltac:(lia));
 pose proof(E 2%nat ltac:(lia));pose proof(E 3%nat ltac:(lia)).
 destruct affine;pose proof(K 0%nat ltac:(lia));pose proof(K 1%nat ltac:(lia));
 pose proof(K 2%nat ltac:(lia));try pose proof(K 3%nat ltac:(lia));
 destruct full, c as [|[|[|c]]];cbn [CachedAddSpec.addition];congruent.
Qed.
Lemma double_result w out q : has_value w q -> input_bounds w ->
 double4_spec w out -> strict out /\ has_value out (fun j=>double_n 4 (q j)).
Proof.
 intros V B S;split;[intros c j C J;exact(proj1(S B j c J C))|].
 intros j J c C;rewrite coord_value by exact C.
 etransitivity;[exact(proj2(S B j c J C))|].
 apply doubles_equivalent;[apply V;exact J|exact C].
Qed.
Lemma add_result (full affine:bool) w cached out q cache :
 has_value w q -> strict w -> cache_bounds affine cached ->
 (forall j c,(j<8)%nat ->(c<(if affine then 3 else 4))%nat ->
    eqm prime (CachedAddSpec.coordinate cached j c)(cache j c)) ->
 CachedAddSpec.cached_add_spec full affine w cached out ->
 strict out /\ has_value out (fun j=>add full affine (q j)(cache j)).
Proof.
 intros V B K Same [_ S];specialize(S (conj (strict_split w B) K)).
 split.
 - intros c j C J i I;destruct(S j c J C) as [Bound _];specialize(Bound i I).
   unfold Double4.Bounds.output_bound;rewrite Nat.mod_small by exact I;exact Bound.
 - intros j J c C;rewrite coord_value by exact C.
   change (eqm prime (CachedAddSpec.coordinate out j c) (coordinate (add full affine (q j)(cache j)) c)).
   apply (eqm_trans prime _ (coordinate(add full affine (point_values w j)
       (CachedAddSpec.coordinate cached j)) c) _).
   + unfold add;rewrite coord_pack by exact C.
     erewrite (CachedAddSpec.addition_ext full affine (coordinate(point_values w j))
       (CachedAddSpec.coordinate cached j) (CachedAddSpec.coordinate w j)
       (CachedAddSpec.coordinate cached j));[exact(proj2(S j c J C))|apply coord_value|auto].
   + apply add_equivalent;auto.
Qed.
