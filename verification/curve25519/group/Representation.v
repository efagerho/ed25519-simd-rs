From Coq Require Import ZArith Znumtheory Ring Field Lia.
From Curve25519 Require Import Edwards.
From Curve25519.group Require Import PrimeField Affine.
Local Open Scope fp_scope.

(* X/Z and Y/Z determine the point. Doubling accepts any incoming T. *)
Definition represents_xyz q P :=
  let z := residue (cz q) in
  z <> 0 /\ residue (cx q) = x P*z /\ residue (cy q) = y P*z.
Definition represents_point (full:bool) q P :=
  represents_xyz q P /\ (full=true -> residue (ct q) = x P*y P*residue (cz q)).

(* Both cache forms use one scale for all components. An affine cache has Z = 1. *)
Definition represents_cache q P := exists z:fp,
  z <> 0 /\ residue (y_minus_x q) = (y P-x P)*z /\
  residue (y_plus_x q) = (y P+x P)*z /\
  residue (t2d q) = (1+1)*d*x P*y P*z /\
  match doubled_z q with None => z=1 | Some zz => residue zz=(1+1)*z end.

Lemma represents_equivalent full q q' P :
 equivalent q q' -> represents_point full q' P -> represents_point full q P.
Proof.
 intros E. unfold represents_point, represents_xyz.
 pose proof (residue_eq _ _ (E 0%nat ltac:(lia))) as X.
 pose proof (residue_eq _ _ (E 1%nat ltac:(lia))) as Y.
 pose proof (residue_eq _ _ (E 2%nat ltac:(lia))) as Zc.
 pose proof (residue_eq _ _ (E 3%nat ltac:(lia))) as T.
 cbn [coordinate] in X,Y,Zc,T. now rewrite X,Y,Zc,T.
Qed.

Local Ltac lift_residues :=
 repeat first [rewrite residue_add | rewrite residue_sub | rewrite residue_mul |
               rewrite residue_opp | rewrite residue_two].

Local Definition completed (full:bool) (e f g h:Z) :=
 Coordinates (e*f) (g*h) (f*g) (if full then e*h else 0)%Z.

(* The x and y quotients may each have their own nonzero common scale.
   Their denominator product is the output Z. *)
Local Lemma completed_sum full e f g h a b P Q :
 let t := d*x P*y P*x Q*y Q in
 a<>0 -> b<>0 ->
 residue g=a*(1+t) -> residue f=b*(1-t) ->
 residue e=a*(x P*y Q+y P*x Q) -> residue h=b*(y P*y Q+x P*x Q) ->
 represents_point full (completed full e f g h) (plus P Q).
Proof.
 intros t A B Gf Ff Ef Hf.
 destruct (denominators _ _ _ _ (on_edwards P) (on_edwards Q)) as [Plus Minus].
 fold t in Plus,Minus.
 assert (X : residue e = x (plus P Q)*residue g).
 { cbn [plus x]; unfold sum_x; fold t; rewrite Gf,Ef; field; exact Plus. }
 assert (Y : residue h = y (plus P Q)*residue f).
 { cbn [plus y]; unfold sum_y; fold t; rewrite Ff,Hf; field; exact Minus. }
 unfold represents_point, represents_xyz, completed; cbn [cx cy cz ct].
 repeat split.
 - rewrite residue_mul,Ff,Gf. exact (mul_nonzero _ _ (mul_nonzero _ _ B Minus) (mul_nonzero _ _ A Plus)).
 - lift_residues. rewrite X. ring.
 - lift_residues. rewrite Y. ring.
 - intros ->; lift_residues. rewrite X,Y. ring.
Qed.

Theorem doubling_represents q P : represents_xyz q P ->
 represents_point true (doubling q) (plus P P).
Proof.
 intros [NZ [X Y]].
 pose proof (on_edwards P) as Curve; unfold on_curve in Curve.
 set (z := residue (cz q)) in *.
 unfold doubling; apply completed_sum with (a:=z*z) (b:=0-z*z).
 - now apply mul_nonzero.
 - intro H; apply (mul_nonzero _ _ NZ NZ).
   replace (z*z) with (0-(0-z*z)) by ring; rewrite H; ring.
 - lift_residues; rewrite X,Y.
   replace (d*x P*y P*x P*y P) with (d*x P*x P*y P*y P) by ring.
   rewrite <-Curve; ring.
 - lift_residues; rewrite X,Y; fold z.
   replace (d*x P*y P*x P*y P) with (d*x P*x P*y P*y P) by ring.
   replace (1 - d*x P*x P*y P*y P) with ((1+1)-(1+d*x P*x P*y P*y P)) by ring.
   rewrite <-Curve; ring.
 - lift_residues; rewrite X,Y; ring.
 - lift_residues; rewrite X,Y; ring.
Qed.

Theorem add_represents full q c P Q :
 represents_point true q P -> represents_cache c Q ->
 represents_point full (add full q c) (plus P Q).
Proof.
 intros [[NZ [X Y]] T] [k [K [Ym [Yp [Td Scale]]]]].
 specialize (T eq_refl).
 set (z := residue (cz q)) in *.
 assert (S : residue (match doubled_z c with
   | None => 2*cz q | Some zz => cz q*zz end)%Z = (1+1)*z*k).
 { destruct (doubled_z c) as [zz|]; lift_residues; fold z.
   - rewrite Scale; ring.
   - rewrite Scale; ring. }
 assert (Nonzero : (1+1)*z*k <> 0).
 { apply mul_nonzero; [apply mul_nonzero; [discriminate|exact NZ]|exact K]. }
 unfold add; apply completed_sum with (a:=(1+1)*z*k) (b:=(1+1)*z*k);
 try exact Nonzero; lift_residues; rewrite ?S,?T,?Td,?Ym,?Yp,?X,?Y; ring.
Qed.

Lemma repeated_doubling_xyz n q P : represents_xyz q P ->
 represents_xyz (double_n n q) (multiple (2^n) P).
Proof.
 intro Valid; induction n as [|n IH].
 - change (represents_xyz q (plus P identity)).
   rewrite (plus_comm P identity), plus_identity.
   exact Valid.
 - replace (2^S n)%nat with (2^n+2^n)%nat by (rewrite Nat.pow_succ_r'; lia).
   rewrite multiple_add. exact (proj1 (doubling_represents _ _ IH)).
Qed.

Corollary double_four_represents q P : represents_xyz q P ->
 represents_point true (double_n 4 q) (multiple 16 P).
Proof.
 intro Valid; change (represents_point true (doubling (double_n 3 q)) (multiple (8+8) P)).
 rewrite multiple_add. apply doubling_represents. exact (repeated_doubling_xyz 3 _ _ Valid).
Qed.

Definition ladder_sum P odd base even :=
 plus (plus (plus (multiple 256 P) (multiple 16 odd)) base) even.

Theorem ladder_represents full q odd base even P Odd Base Even :
 represents_xyz q P -> represents_cache odd Odd ->
 represents_cache base Base -> represents_cache even Even ->
 represents_point full (ladder_formula full q odd base even)
   (ladder_sum P Odd Base Even).
Proof.
 intros Valid O B E; unfold ladder_formula.
 pose proof (add_represents false _ _ _ _ (double_four_represents _ _ Valid) O) as First.
 pose proof (double_four_represents _ _ (proj1 First)) as Second.
 rewrite multiple_sum, multiple_multiple in Second.
 apply add_represents; [now apply add_represents|exact E].
Qed.
