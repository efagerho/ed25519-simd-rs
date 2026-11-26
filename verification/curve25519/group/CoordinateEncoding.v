(* Coordinate encodings of the same affine Edwards group used by the ladder. *)
From Coq Require Import ZArith Field.
From Coqprime.elliptic Require GZnZ.
From Curve25519 Require Import Edwards.
From Curve25519.group Require Import PrimeField Affine Representation.
Local Open Scope fp_scope.
Local Notation val := (GZnZ.val Field.prime).

Lemma scaled_coordinate_eq (z a b : fp) : z <> 0 -> (a*z = b*z <-> a = b).
Proof.
 intro NZ. split; [intro E | intros ->; reflexivity].
 replace a with ((a*z)/z) by (field; exact NZ). rewrite E; field; exact NZ.
Qed.

Local Lemma residue_val a : residue (val a) = a.
Proof. destruct a as [n E]; apply GZnZ.zirr; symmetry; exact E. Qed.

Definition extended_at P z :=
 Coordinates (val (x P*z)) (val (y P*z)) (val z) (val (x P*y P*z)).

Lemma extended_at_correct full P z : z <> 0 -> represents_point full (extended_at P z) P.
Proof.
 intro NZ. unfold represents_point, represents_xyz, extended_at.
 cbn [cx cy cz ct]; rewrite !residue_val; auto.
Qed.

Lemma xyz_unique q P R : represents_xyz q P -> represents_xyz q R -> P = R.
Proof.
 intros [NZ [XP YP]] [_ [XR YR]]. apply point_ext; split;
   apply (proj1 (scaled_coordinate_eq (residue (cz q)) _ _ NZ)); congruence.
Qed.

(* An absent scale tag denotes the affine cache. A projective cache stores 2Z. *)
Definition cache_at P (scale : option fp) :=
 let z := match scale with Some s => s | None => 1 end in
 CachedCoordinates (val ((y P-x P)*z)) (val ((y P+x P)*z))
   (val ((1+1)*d*x P*y P*z)) (option_map (fun s => val ((1+1)*s)) scale).

Lemma cache_at_correct P scale : (forall z, scale = Some z -> z <> 0) ->
 represents_cache (cache_at P scale) P.
Proof.
 intro NZ; destruct scale as [z|]; [exists z|exists 1];
   cbn [cache_at y_minus_x y_plus_x t2d doubled_z option_map]; rewrite !residue_val;
   repeat split; auto; discriminate.
Qed.

Lemma cache_unique q P R : represents_cache q P -> represents_cache q R -> P = R.
Proof.
 intros [z [NZ [MP [PP [_ ZP]]]]] [t [_ [MR [PR [_ ZR]]]]].
 assert (z=t) as ->.
 { destruct (doubled_z q); [|congruence].
   apply (proj1 (scaled_coordinate_eq (1+1) _ _ ltac:(discriminate))).
   replace (z*(1+1)) with ((1+1)*z) by ring.
   replace (t*(1+1)) with ((1+1)*t) by ring. congruence. }
 assert (M : y P-x P = y R-x R) by (apply (proj1 (scaled_coordinate_eq t _ _ NZ)); congruence).
 assert (S : y P+x P = y R+x R) by (apply (proj1 (scaled_coordinate_eq t _ _ NZ)); congruence).
 apply point_ext; split; apply (proj1 (scaled_coordinate_eq (1+1) _ _ ltac:(discriminate))).
 - replace (x P*(1+1)) with ((y P+x P)-(y P-x P)) by ring. rewrite M,S; ring.
 - replace (y P*(1+1)) with ((y P+x P)+(y P-x P)) by ring. rewrite M,S; ring.
Qed.

(* A projective table row for P or -P, built directly from extended X,Y,Z,T. *)
Lemma signed_cache_from_extended (positive : bool) q P u v t zz :
 represents_point true q P ->
 residue u = (if positive then residue (cy q)-residue (cx q)
               else residue (cy q)+residue (cx q)) ->
 residue v = (if positive then residue (cy q)+residue (cx q)
               else residue (cy q)-residue (cx q)) ->
 residue t = (if positive then residue (ct q)*((1+1)*d)
               else -(residue (ct q)*((1+1)*d))) ->
 residue zz = residue (cz q)+residue (cz q) ->
 represents_cache (CachedCoordinates u v t (Some zz)) (if positive then P else negative P).
Proof.
 intros [[NZ [X Y]] T] U V Dt Z2. specialize (T eq_refl).
 exists (residue (cz q)). split; [exact NZ|].
 destruct positive; cbn [y_minus_x y_plus_x t2d doubled_z negative x y] in *;
 rewrite U,V,Dt,Z2,X,Y,T; repeat split; ring.
Qed.

Lemma unit_cache_affine u v t zz P :
 represents_cache (CachedCoordinates u v t (Some zz)) P -> residue zz = 1+1 ->
 represents_cache (CachedCoordinates u v t None) P.
Proof.
 intros [z [NZ [U [V [T Z2]]]]] Unit. exists z. repeat split; auto.
 apply (proj1 (scaled_coordinate_eq (1+1) _ _ ltac:(discriminate))).
 cbn [doubled_z] in Z2. replace (z*(1+1)) with ((1+1)*z) by ring.
 rewrite <-Z2, Unit; ring.
Qed.

Lemma cache_seed_xyz u v t zz P :
 represents_cache (CachedCoordinates u v t (Some zz)) P ->
 represents_xyz (Coordinates (v-u) (v+u) zz 0) P.
Proof.
 intros [z [NZ [U [V [_ D]]]]].
 unfold represents_xyz; cbn [cx cy cz y_minus_x y_plus_x doubled_z] in *.
 rewrite residue_sub,residue_add,U,V,D. split; [apply mul_nonzero; [discriminate|assumption]|split; ring].
Qed.

Lemma cache_identity_iff u v t zz P :
 represents_cache (CachedCoordinates u v t (Some zz)) P ->
 (residue v = residue u /\ residue u+residue u = residue zz <-> P = identity).
Proof.
 intro Cache. destruct (cache_seed_xyz _ _ _ _ _ Cache) as [NZ [X Y]].
 cbn [cx cy cz] in *. rewrite residue_sub in X. rewrite residue_add in Y.
 split.
 - intros [UV D]. apply point_ext; split; cbn [x y identity];
   apply (proj1 (scaled_coordinate_eq _ _ _ NZ)).
   + rewrite <-X, UV; ring.
   + rewrite <-Y, UV, D; ring.
 - intros ->. cbn [identity x y] in X,Y.
   assert (E : residue v = residue u).
   { replace (residue v) with ((residue v-residue u)+residue u) by ring. rewrite X; ring. }
   split; [exact E|]. rewrite E in Y. rewrite Y; ring.
Qed.
