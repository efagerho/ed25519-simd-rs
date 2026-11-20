From Coq Require Import ZArith Ring Field Eqdep_dec.
From Curve25519.group Require Import PrimeField.
Local Open Scope fp_scope.

Definition on_curve (x y:fp) := y*y-x*x = 1+d*x*x*y*y.

Local Lemma square_ratio n b c : b<>0 -> n*n = c*(b*b) -> (n/b)*(n/b)=c.
Proof. intros B H. field_simplify_eq; [rewrite H; ring|exact B]. Qed.

(* If the product in the denominators were +1 or -1, a square root of
   d could be read off from one of the two curve equations. *)
Lemma denominators x y u v : on_curve x y -> on_curve u v ->
  1 + d*x*y*u*v <> 0 /\ 1 - d*x*y*u*v <> 0.
Proof.
 unfold on_curve; intros P Q.
 set (t := d*x*y*u*v).
 assert (regular : t*t <> 1).
 { intro Bad.
   assert (product : x*y*u*v <> 0).
   { intro Zero; unfold t in Bad.
     replace (d*x*y*u*v) with (d*(x*y*u*v)) in Bad by ring.
     rewrite Zero in Bad; ring_simplify in Bad; discriminate. }
   assert (nz : forall a b:fp, a*b<>0 -> a<>0 /\ b<>0).
   { intros a b H; split; intros ->; apply H; ring. }
   destruct (nz _ _ product) as [XYU V].
   destruct (nz _ _ XYU) as [XY U].
   destruct (nz _ _ XY) as [X Y].
   set (k := d*x*x*y*y).
   assert (factor : (y*y-k*v*v)*(y*y+k*u*u) = 0).
   { replace ((y*y-k*v*v)*(y*y+k*u*u)) with
       (y*y*((y*y-x*x)-k*(v*v-u*u)) + x*x*y*y*(1-t*t))
       by (unfold k,t; ring).
     rewrite P,Q,Bad. fold k.
     replace (1+k-k*(1+d*u*u*v*v)) with (1-t*t) by (unfold k,t;ring).
     rewrite Bad; ring. }
   destruct (fp_eq_dec (y*y-k*v*v) 0) as [A|A].
   - apply (d_nonsquare (y/(x*y*v))).
     unfold k in A. apply square_ratio; [repeat apply mul_nonzero; assumption|].
     transitivity ((y*y-d*x*x*y*y*v*v) + d*((x*y*v)*(x*y*v))); [ring|rewrite A; ring].
   - assert (B : y*y+k*u*u = 0).
     { destruct (fp_eq_dec (y*y+k*u*u) 0) as [Zero|Nonzero]; [exact Zero|].
       exfalso; exact (mul_nonzero _ _ A Nonzero factor). }
     set (i := residue Field.sqrt_m1).
     apply (d_nonsquare (i*y/(x*y*u))).
     unfold k in B. apply square_ratio; [repeat apply mul_nonzero; assumption|].
     replace ((i*y)*(i*y)) with ((i*i)*(y*y)) by ring; rewrite (sqrt_m1_square : i*i = 0-1).
     replace ((0-1)*(y*y)) with
       (d*((x*y*u)*(x*y*u)) - (y*y + d*x*x*y*y*u*u)) by ring.
     rewrite B; ring.
 }
 split; intro H; apply regular.
 - replace t with ((1+t)-1) by ring; rewrite H; ring.
 - replace t with (1-(1-t)) by ring; rewrite H; ring.
Qed.

(* Affine twisted-Edwards addition, RFC 8032 sections 3.2 and 5.1. *)
Record point := Point { x : fp; y : fp; on_edwards : on_curve x y }.
Definition sum_x x y u v := (x*v+y*u)/(1+d*x*y*u*v).
Definition sum_y x y u v := (y*v+x*u)/(1-d*x*y*u*v).

Local Lemma curve_fraction a b c e : c<>0 -> e<>0 ->
 b*b*c*c-a*a*e*e=c*c*e*e+d*a*a*b*b -> on_curve (a/c) (b/e).
Proof.
 unfold on_curve; intros C E H.
 field_simplify_eq; [|auto].
 transitivity (b*b*c*c-a*a*e*e); [ring|rewrite H; ring].
Qed.

Local Lemma curve_polynomial x y : on_curve x y ->
 d*x*x*y*y = y*y-x*x-1.
Proof. unfold on_curve; intro H; rewrite H; ring. Qed.

Lemma sum_on_curve x y u v : on_curve x y -> on_curve u v ->
  on_curve (sum_x x y u v) (sum_y x y u v).
Proof.
 intros P Q; destruct (denominators _ _ _ _ P Q) as [Plus Minus].
 unfold sum_x, sum_y. apply curve_fraction; try assumption.
 pose proof (curve_polynomial _ _ P) as A; pose proof (curve_polynomial _ _ Q) as B.
 ring [A B].
Qed.

Definition plus P Q := Point _ _ (sum_on_curve _ _ _ _ (on_edwards P) (on_edwards Q)).
Definition identity := Point 0 1 ltac:(unfold on_curve; ring).
Lemma point_ext P Q : x P = x Q /\ y P = y Q -> P = Q.
Proof.
 destruct P as [x y H], Q as [u v K]; intros [X Y]; cbn in X,Y; subst.
 f_equal. apply Eqdep_dec.eq_proofs_unicity. intros a b; destruct (fp_eq_dec a b); auto.
Qed.

Lemma plus_comm P Q : plus P Q = plus Q P.
Proof.
 destruct P as [px py P], Q as [u v Q].
 apply point_ext; cbn [plus x y]; unfold sum_x, sum_y; split; f_equal; ring.
Qed.
Lemma plus_identity P : plus identity P = P.
Proof.
 destruct P as [px py P]; apply point_ext; cbn [plus identity x y]; unfold sum_x, sum_y.
 replace (d*0*1*px*py) with 0 by ring. split; field; discriminate.
Qed.

Definition negative (P : point) : point.
Proof.
 refine (Point (-x P) (y P) _).
 pose proof (on_edwards P) as H; unfold on_curve in *.
 transitivity (y P*y P - x P*x P); [ring|rewrite H; ring].
Defined.

Lemma plus_negative P : plus P (negative P) = identity.
Proof.
 apply point_ext; cbn [plus identity negative x y]; unfold sum_x, sum_y.
 destruct (denominators _ _ _ _ (on_edwards P) (on_edwards (negative P))) as [A B].
 cbn [negative x y] in A,B.
 pose proof (curve_polynomial _ _ (on_edwards P)) as C.
 split; field_simplify_eq; first [reflexivity|ring [C]|assumption].
Qed.

(* A pair of fractions keeps the two affine denominators nonzero while
   clearing them from the associativity identity. *)
Record fractions := Fractions { xn:fp; xd:fp; yn:fp; yd:fp }.
Local Definition represents_fractions f P :=
 xd f<>0 /\ yd f<>0 /\ xn f=x P*xd f /\ yn f=y P*yd f.
Local Definition sum_fractions P Q :=
 let t := d*x P*y P*x Q*y Q in
 Fractions (x P*y Q+y P*x Q) (1+t) (y P*y Q+x P*x Q) (1-t).
Local Lemma sum_fractions_ok P Q : represents_fractions (sum_fractions P Q) (plus P Q).
Proof.
 destruct (denominators _ _ _ _ (on_edwards P) (on_edwards Q)) as [A B].
 unfold represents_fractions, sum_fractions; cbn [plus x y xn yn xd yd].
 unfold sum_x, sum_y; repeat split; try assumption; field; assumption.
Qed.
Local Definition add_fraction_point f R :=
 let a := xn f in let b := yn f in let c := xd f in let e := yd f in
 let t := d*a*b*x R*y R in
 Fractions (a*e*y R+b*c*x R) (c*e+t) (b*c*y R+a*e*x R) (c*e-t).
Local Lemma add_fraction_point_ok f P R : represents_fractions f P ->
 represents_fractions (add_fraction_point f R) (plus P R).
Proof.
 destruct f as [a c b e]; unfold represents_fractions, add_fraction_point; cbn [xn yn xd yd].
 intros [C [E [-> ->]]].
 destruct (sum_fractions_ok P R) as [Plus [Minus [X Y]]].
 unfold sum_fractions in Plus,Minus,X,Y; cbn [xn yn xd yd] in Plus,Minus,X,Y.
 set (t:=d*x P*y P*x R*y R) in *.
 replace (c*e+d*(x P*c)*(y P*e)*x R*y R) with ((1+t)*(c*e)) by (unfold t;ring).
 replace (c*e-d*(x P*c)*(y P*e)*x R*y R) with ((1-t)*(c*e)) by (unfold t;ring).
 split; [exact (mul_nonzero _ _ Plus (mul_nonzero _ _ C E))|].
 split; [exact (mul_nonzero _ _ Minus (mul_nonzero _ _ C E))|].
 split.
 - replace (x (plus P R)*((1+t)*(c*e))) with ((x (plus P R)*(1+t))*(c*e)) by ring.
   rewrite <-X; ring.
 - replace (y (plus P R)*((1-t)*(c*e))) with ((y (plus P R)*(1-t))*(c*e)) by ring.
   rewrite <-Y; ring.
Qed.

Local Lemma cross_equal (a b c e u v:fp) : c<>0 -> e<>0 ->
 a=u*c -> b=v*e -> a*e=b*c -> u=v.
Proof.
 intros C E -> -> H.
 transitivity (((u*c)*e)/(c*e)); [field;auto|rewrite H;field;auto].
Qed.
Lemma plus_assoc P Q R : plus (plus P Q) R = plus P (plus Q R).
Proof.
 pose proof (add_fraction_point_ok _ _ R (sum_fractions_ok P Q)) as [Lx [Ly [X Y]]].
 pose proof (add_fraction_point_ok _ _ P (sum_fractions_ok Q R)) as [Rx [Ry [U V]]].
 pose proof (curve_polynomial _ _ (on_edwards P)) as A.
 pose proof (curve_polynomial _ _ (on_edwards Q)) as B.
 pose proof (curve_polynomial _ _ (on_edwards R)) as C.
 rewrite (plus_comm P (plus Q R)). apply point_ext; split.
 - eapply cross_equal; [exact Lx|exact Rx|exact X|exact U|].
   unfold add_fraction_point, sum_fractions; cbn [xn xd yn yd]; ring [A B C].
 - eapply cross_equal; [exact Ly|exact Ry|exact Y|exact V|].
   unfold add_fraction_point, sum_fractions; cbn [xn xd yn yd]; ring [A B C].
Qed.

Fixpoint multiple (n:nat) P := match n with
 | O => identity | S k => plus P (multiple k P) end.

Lemma multiple_add n m P :
 multiple (n+m) P = plus (multiple n P) (multiple m P).
Proof.
 induction n; cbn [Nat.add multiple].
 - symmetry; apply plus_identity.
 - rewrite IHn; symmetry; apply plus_assoc.
Qed.

Lemma multiple_sum n P Q :
 multiple n (plus P Q) = plus (multiple n P) (multiple n Q).
Proof.
 induction n; cbn [multiple].
 - symmetry; apply plus_identity.
 - rewrite IHn, !plus_assoc. f_equal. rewrite <-!plus_assoc. f_equal. apply plus_comm.
Qed.
Lemma multiple_multiple n m P : multiple n (multiple m P) = multiple (n*m) P.
Proof. induction n; cbn [multiple Nat.mul]; [reflexivity|now rewrite IHn,multiple_add]. Qed.
