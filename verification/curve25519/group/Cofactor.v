From Coq Require Import ZArith Field Ring.
From Curve25519 Require Import Edwards Torsion.
From Curve25519.group Require Import PrimeField Affine Representation.
Local Open Scope fp_scope.

Local Lemma quotient_zero (a b : fp) : b <> 0 -> (a/b = 0 <-> a = 0).
Proof.
 intros B; split.
 - intro H. replace a with ((a/b)*b) at 1 by (field; exact B). rewrite H; ring.
 - intros ->; field; exact B.
Qed.

Local Lemma twice P : multiple 2 P = plus P P.
Proof.
 change (plus P (plus P identity) = plus P P).
 now rewrite (plus_comm P identity), plus_identity.
Qed.

Local Lemma double_identity_iff P : plus P P = identity <-> x P = 0.
Proof.
 split.
 - intro H.
   assert (Same : P = negative P).
   { rewrite <- (plus_identity (negative P)), <- H, plus_assoc, plus_negative.
     rewrite (plus_comm P identity); symmetry; apply plus_identity. }
   apply (f_equal x) in Same. change (x P = -x P) in Same.
   assert (Zero : (1+1)*x P = 0).
   { replace ((1+1)*x P) with (x P-(-x P)) by ring. rewrite <- Same; ring. }
   apply product_zero in Zero as [Bad|X]; [discriminate|exact X].
 - intro X. assert (Same : P = negative P).
   { apply point_ext; cbn [negative x y]; split; [rewrite X; ring|reflexivity]. }
   rewrite Same at 2. apply plus_negative.
Qed.

(* The determinant detects exactly the differences killed by 2. It uses
   only XYZ, with independent nonzero projective scales for the two inputs. *)
Theorem torsion_shortcut_iff q r P R :
 represents_xyz q P -> represents_xyz r R ->
 ((torsion_determinant q r mod Field.prime = 0)%Z <->
  multiple 2 (plus P (negative R)) = identity).
Proof.
 intros [Zp [X Y]] [Zr [U V]].
 unfold torsion_determinant. rewrite residue_zero, residue_sub, !residue_mul, X,Y,U,V.
 rewrite twice, double_identity_iff.
 destruct (denominators _ _ _ _ (on_edwards P) (on_edwards (negative R))) as [D _].
 cbn [negative x y] in D. cbn [plus negative x y]; unfold sum_x.
 rewrite quotient_zero by exact D.
 set (z := residue (cz q)) in *; set (w := residue (cz r)) in *.
 replace (x P*z*(y R*w)-y P*z*(x R*w)) with ((x P*y R+y P*(-x R))*(z*w)) by ring.
 rewrite product_zero. pose proof (mul_nonzero _ _ Zp Zr). tauto.
Qed.

Local Lemma double_x_zero P : x (plus P P) = 0 <-> x P = 0 \/ y P = 0.
Proof.
 destruct (denominators _ _ _ _ (on_edwards P) (on_edwards P)) as [D _].
 cbn [plus x]; unfold sum_x. rewrite quotient_zero by exact D.
 replace (x P*y P + y P*x P) with ((1+1)*(x P*y P)) by ring.
 rewrite !product_zero. split; [intros [Bad|H]; [discriminate|exact H]|auto].
Qed.

Local Lemma double_y_zero P :
 y (plus P P) = 0 <-> x P*x P + y P*y P = 0.
Proof.
 destruct (denominators _ _ _ _ (on_edwards P) (on_edwards P)) as [_ D].
 cbn [plus y]; unfold sum_y. rewrite quotient_zero by exact D.
 replace (y P*y P+x P*x P) with (x P*x P+y P*y P) by ring. reflexivity.
Qed.

Theorem eight_identity_iff P :
 multiple 8 P = identity <-> x P*y P*(x P*x P+y P*y P) = 0.
Proof.
 change 8%nat with (4+4)%nat.
 rewrite multiple_add, double_identity_iff.
 change 4%nat with (2+2)%nat.
 rewrite multiple_add, double_x_zero.
 rewrite twice, double_x_zero, double_y_zero, !product_zero. tauto.
Qed.

Lemma torsion_roots_iff xx yy :
 torsion_roots xx yy <->
 residue xx * residue yy * (residue xx * residue xx + residue yy * residue yy) = 0.
Proof.
 unfold torsion_roots. rewrite !residue_zero, residue_add, residue_sub, !residue_mul.
 set (i := residue Field.sqrt_m1). set (a := residue xx). set (b := residue yy).
 replace (a*a+b*b) with ((i*b+a)*(a-i*b)).
 2: { transitivity (a*a-(i*i)*(b*b)); [ring|rewrite (sqrt_m1_square : i*i = 0-1); ring]. }
 assert (swap : i*b-a = 0 <-> a-i*b = 0).
 { split; intro H; [replace (a-i*b) with (0-(i*b-a)) by ring |
                     replace (i*b-a) with (0-(a-i*b)) by ring]; rewrite H; ring. }
 rewrite swap, !product_zero. assert (i <> 0) by discriminate. tauto.
Qed.

(* The assembly's two numerators are projective X and Y of P-R with
   the same nonzero scale. Completeness of Edwards addition supplies both
   nonzero denominators, including when P=R or the difference is torsion. *)
Lemma torsion_numerators_represent q r P R :
 represents_point true q P -> represents_point true r R -> residue (cz r) = 1 ->
 let '(xx, yy) := torsion_numerators q r in
 exists s : fp, s <> 0 /\
   residue xx = x (plus P (negative R))*s /\
   residue yy = y (plus P (negative R))*s.
Proof.
 intros [[NZ [X Y]] T] [[_ [U V]] RT] AffineR.
 specialize (T eq_refl); specialize (RT eq_refl).
 rewrite AffineR in U,V,RT.
 assert (Rx : residue (cx r) = x R) by (rewrite U; ring).
 assert (Ry : residue (cy r) = y R) by (rewrite V; ring).
 assert (Rt : residue (ct r) = x R*y R) by (rewrite RT; ring).
 set (z := residue (cz q)) in *.
 set (w := d*x P*y P*x R*y R).
 set (c := residue 121666). set (n := residue 121665).
 assert (C : c <> 0) by discriminate.
 assert (CD : c*d = -n) by (unfold c, n, d; field; discriminate).
 assert (ScaledT : n*(x P*y P*z*(x R*y R)) = -(c*z*w)).
 { unfold w. replace (c*z*(d*x P*y P*x R*y R))
     with ((c*d)*(x P*y P*z*(x R*y R))) by ring. rewrite CD; ring. }
 destruct (denominators _ _ _ _ (on_edwards P) (on_edwards R)) as [Dp Dm].
 fold w in Dp, Dm.
 exists (c*z*z*(1-w)*(1+w)). split.
 - repeat first [assumption | apply mul_nonzero].
 - unfold torsion_numerators, torsion_determinant.
   repeat first [rewrite residue_add | rewrite residue_sub | rewrite residue_mul].
   rewrite X,Y,T,Rx,Ry,Rt; fold c n z; rewrite ScaledT.
   cbn [plus negative x y]; unfold sum_x, sum_y.
   replace (1+d*x P*y P*(-x R)*y R) with (1-w) by (unfold w; ring).
   replace (1-d*x P*y P*(-x R)*y R) with (1+w) by (unfold w; ring).
   split; field; assumption.
Qed.

(* The full per-lane predicate works both after a missed shortcut and in
   lanes where the shortcut held but another lane required the full check. *)
Theorem torsion_check_correct q r P R :
 represents_point true q P -> represents_point true r R -> residue (cz r) = 1 ->
 (torsion_check q r <-> multiple 8 (plus P (negative R)) = identity).
Proof.
 intros Q A AffineR.
 pose proof (torsion_numerators_represent q r P R Q A AffineR) as Scaled.
 unfold torsion_check. destruct (torsion_numerators q r) as [xx yy].
 destruct Scaled as [s [NZ [X Y]]].
 rewrite torsion_roots_iff, eight_identity_iff, X, Y.
 set (a := x (plus P (negative R))); set (b := y (plus P (negative R))).
 replace (a*s*(b*s)*(a*s*(a*s)+b*s*(b*s))) with
     ((a*b*(a*a+b*b))*(s*s*s*s)) by ring.
 rewrite (product_zero (a*b*(a*a+b*b))).
 assert (s*s*s*s <> 0) by (repeat first [assumption | apply mul_nonzero]). tauto.
Qed.

Corollary torsion_shortcut q r P R :
 represents_xyz q P -> represents_xyz r R ->
 (torsion_determinant q r mod Field.prime = 0)%Z ->
 multiple 8 (plus P (negative R)) = identity.
Proof.
 intros Q A E. apply (proj1 (torsion_shortcut_iff q r P R Q A)) in E.
 change 8%nat with (4*2)%nat. rewrite <- multiple_multiple, E.
 cbn [multiple]; repeat rewrite plus_identity; reflexivity.
Qed.

Lemma equal_points_determinant q r P :
 represents_xyz q P -> represents_xyz r P ->
 (torsion_determinant q r mod Field.prime = 0)%Z.
Proof.
 intros [_ [X Y]] [_ [U V]]. apply residue_zero.
 unfold torsion_determinant. rewrite residue_sub, !residue_mul, X,Y,U,V. ring.
Qed.
