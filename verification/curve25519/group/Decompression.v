From Coq Require Import ZArith Znumtheory Lia Field Bool.
From Coqprime.PrimalityTest Require Import Euler Zp.
From Coqprime.Z Require Import ZCAux.
From Coqprime.elliptic Require GZnZ.
From Curve25519.group Require Import PrimeField Affine.
Local Open Scope fp_scope.
Local Notation p := Field.prime.
Local Notation val := (GZnZ.val p).

Definition exponent := Field.sqrt_ratio_exponent.
Definition power (a:fp) (n:Z) := residue (val a ^ n).

Local Lemma power_one a : power a 1 = a.
Proof. unfold power. rewrite Z.pow_1_r. destruct a as [z Hz]. apply GZnZ.zirr. symmetry; exact Hz. Qed.
Local Lemma power_add a n m : (0<=n)%Z ->
 (0<=m)%Z -> power a (n+m) = power a n * power a m.
Proof. intros N M. unfold power. rewrite Z.pow_add_r by auto. apply residue_mul. Qed.
Local Lemma power_square (a:fp) n : (0<=n)%Z ->
 power (a*a) n = power a (2*n).
Proof.
 intro N. apply GZnZ.zirr. change ((((val a * val a) mod p)^n) mod p =
   (val a ^ (2*n)) mod p)%Z.
 rewrite Z.pow_mul_r by lia. replace (val a ^ 2)%Z with (val a * val a)%Z by ring.
 symmetry. apply Zpower_mod. unfold Field.prime; lia.
Qed.
Local Lemma fermat a : a<>0 -> power a (p-1) = 1.
Proof.
 intros NZ. assert (Range : (0 <= val a < p)%Z).
 { rewrite (GZnZ.inZnZ p a). apply Z.mod_pos_bound. unfold Field.prime; lia. }
 assert (Pos : (0 < val a)%Z).
 { destruct (Z.eq_dec (val a) 0); [exfalso; destruct a; apply NZ; apply GZnZ.zirr; exact e|lia]. }
 pose proof (phi_power_is_1 (val a) p ltac:(unfold Field.prime;lia)
   (rel_prime_le_prime (val a) p modulus_prime ltac:(lia))) as H.
 rewrite (prime_phi_n_minus_1 p modulus_prime) in H. apply GZnZ.zirr. exact H.
Qed.

Lemma power_inverse a : a<>0 -> power a (p-2) = 1/a.
Proof.
 intro NZ. pose proof (fermat a NZ) as H.
 replace (p-1)%Z with ((p-2)+1)%Z in H by ring.
 rewrite power_add, power_one in H by (unfold Field.prime;lia).
 transitivity ((power a (p-2)*a)/a); [field;exact NZ|now rewrite H].
Qed.

Definition numerator (y:fp) := residue 121666 * (y*y-1).
Definition denominator (y:fp) := y*y - numerator y.
Definition test_value (u v t:fp) := u*v*(t*t).

Local Lemma scale_nonzero : residue 121666 <> 0.
Proof. discriminate. Qed.
Local Lemma ratio_curve x y :
 denominator y * (x*x) = numerator y <-> on_curve x y.
Proof.
 unfold on_curve, denominator, numerator, d.
 set (c:=residue 121666). assert (C : c<>0) by exact scale_nonzero.
 assert (K : residue 121665 = c-1) by (apply GZnZ.zirr; reflexivity).
 rewrite K. split; intro H.
 - field_simplify_eq; [|exact C].
   match goal with H : ?l = ?r |- ?a = ?b => first [replace a with ((l-r)+b) by ring | replace a with ((r-l)+b) by ring]; rewrite H; ring end.
 - field_simplify_eq in H; try exact C.
   match goal with H : ?l = ?r |- ?a = ?b => first [replace a with ((l-r)+b) by ring | replace a with ((r-l)+b) by ring]; rewrite H; ring end.
Qed.

Local Lemma square_test u v x : u<>0 -> v*(x*x)=u ->
 let t := power (u*v) exponent in
 test_value u v t = 1 \/ test_value u v t = 0-1.
Proof.
 intros U X t. set (a:=v*x).
 assert (A : a<>0).
 { intro Zr. apply U. rewrite <- X. replace (v*(x*x)) with (a*x) by (unfold a;ring).
   rewrite Zr; ring. }
 assert (UV : u*v = a*a) by (rewrite <- X; unfold a; ring).
 set (q:=test_value u v t).
 assert (Q : q=power (a*a) (1+(exponent+exponent))).
 { unfold q,test_value,t. rewrite UV.
   rewrite !power_add by (vm_compute; discriminate).
   now rewrite power_one. }
 assert (Unity : q*q=1).
 { rewrite Q, power_square by (vm_compute; discriminate).
   rewrite <- power_add by (vm_compute; discriminate).
   change (power a (p-1)=1). now apply fermat. }
 assert (Factor : (q-1)*(q+1)=0).
 { replace ((q-1)*(q+1)) with (q*q-1) by ring. rewrite Unity; ring. }
 apply product_zero in Factor as [F|F].
 - left. change (q=1). replace q with ((q-1)+1) by ring. rewrite F; ring.
 - right. change (q=0-1). replace q with ((q+1)-1) by ring. rewrite F; ring.
Qed.

Definition parity (x:fp) := Z.odd (val x).
Definition signed_root sign (x:fp) := if Bool.eqb (parity x) sign then x else -x.
Definition has_sign sign (x:fp) := x=0 \/ parity x=sign.

Local Lemma opposite_parity x : x<>0 -> parity (-x) = negb (parity x).
Proof.
 intro NZ. assert (Range : (0 <= val x < p)%Z).
 { rewrite (GZnZ.inZnZ p x). apply Z.mod_pos_bound. unfold Field.prime;lia. }
 assert (Pos : (0 < val x)%Z).
 { destruct (Z.eq_dec (val x) 0) as [Zr|]; [exfalso;destruct x;apply NZ,GZnZ.zirr;exact Zr|lia]. }
 assert (Neg : val (-x) = (p-val x)%Z).
 { change ((-val x) mod p = p-val x)%Z.
   replace (-val x)%Z with ((p-val x)+(-1)*p)%Z by ring.
   rewrite Z.mod_add, Z.mod_small by lia. reflexivity. }
 unfold parity. rewrite Neg,Z.odd_sub. change (xorb true (Z.odd (val x)) = negb (Z.odd (val x))).
 destruct (Z.odd (val x));reflexivity.
Qed.
Local Lemma signed_root_ok sign x :
 signed_root sign x * signed_root sign x = x*x /\ has_sign sign (signed_root sign x).
Proof.
 unfold signed_root,has_sign. destruct (Bool.eqb (parity x) sign) eqn:S.
 - apply (proj1 (Bool.eqb_true_iff _ _)) in S. split; [reflexivity|right;exact S].
 - split; [ring|]. destruct (fp_eq_dec x 0) as [->|NZ]; [left;ring|right].
   rewrite opposite_parity by exact NZ. destruct (parity x),sign;easy.
Qed.

Lemma unique_signed_root sign x z y : on_curve x y -> on_curve z y ->
 has_sign sign x -> has_sign sign z -> x=z.
Proof.
 intros X Zr Hx Hz. apply ratio_curve in X,Zr.
 assert (V:denominator y<>0).
 { intro Bad. rewrite Bad in X. assert (U:numerator y=0) by (rewrite <-X;ring).
   unfold denominator in Bad;rewrite U in Bad.
   unfold numerator in U. apply product_zero in U as [C|YY];[contradiction scale_nonzero|].
   assert (One:y*y=1) by (replace (y*y) with ((y*y-1)+1) by ring;rewrite YY;ring).
   rewrite One in Bad;discriminate. }
 assert (F:(x-z)*(x+z)=0).
 { assert (D:denominator y*((x-z)*(x+z))=0).
   { replace (denominator y*((x-z)*(x+z))) with (denominator y*(x*x)-denominator y*(z*z)) by ring.
     rewrite X,Zr;ring. }
   destruct(proj1(product_zero _ _) D);tauto. }
 destruct(proj1(product_zero _ _) F) as [Same|Opp].
 - replace x with ((x-z)+z) by ring;rewrite Same;ring.
 - assert (E:x= -z) by (replace x with ((x+z)-z) by ring;rewrite Opp;ring).
   subst x. destruct (fp_eq_dec z 0) as [->|NZ];[ring|].
   destruct Hx as [H|H],Hz as [Z0|Z0];try contradiction.
   + exfalso;apply NZ;replace z with (-(-z)) by ring;rewrite H;ring.
   + rewrite opposite_parity,Z0 in H by exact NZ. destruct sign;discriminate.
Qed.

(* The compressed integer may encode any y below 2^255. Its high bit selects
   the parity of the canonical x, with both signs accepted for x = 0. *)
Definition decode (y:fp) (sign:bool) : option fp :=
 let u:=numerator y in let v:=denominator y in
 let t:=power (u*v) exponent in let q:=test_value u v t in
 let x:=u*t in
 if fp_eq_dec q (0-1) then Some (signed_root sign (x*residue Field.sqrt_m1))
 else if fp_eq_dec q 1 then Some (signed_root sign x)
 else if fp_eq_dec u 0 then Some (signed_root sign x) else None.

Theorem decode_correct y sign :
 match decode y sign with
 | Some x => on_curve x y /\ has_sign sign x
 | None => forall x, ~on_curve x y
 end.
Proof.
 unfold decode. set (u:=numerator y). set (v:=denominator y).
 set (t:=power (u*v) exponent). set (q:=test_value u v t).
 assert (Root : v*((u*t)*(u*t))=u*q) by (unfold q,test_value;ring).
 destruct (fp_eq_dec q (0-1)) as [M|M].
 - destruct (signed_root_ok sign (u*t*residue Field.sqrt_m1)) as [S H].
   split; [apply ratio_curve|exact H]. fold u v. rewrite S.
   replace (v*(u*t*residue Field.sqrt_m1*(u*t*residue Field.sqrt_m1))) with
    ((v*((u*t)*(u*t)))*(residue Field.sqrt_m1*residue Field.sqrt_m1)) by ring.
   rewrite Root,M,sqrt_m1_square. ring.
 - destruct (fp_eq_dec q 1) as [P|P].
   + destruct (signed_root_ok sign (u*t)) as [S H]. split; [apply ratio_curve|exact H].
     fold u v. rewrite S,Root,P. ring.
   + destruct (fp_eq_dec u 0) as [Zr|NZ].
     * destruct (signed_root_ok sign (u*t)) as [S H]. split; [apply ratio_curve|exact H].
       fold u v. rewrite S,Root,Zr; ring.
     * intros x On. apply ratio_curve in On.
       destruct (square_test u v x NZ On); contradiction.
Qed.

Local Open Scope Z_scope.
Lemma pow_value a e : 0<=e -> residue (a^e)=power (residue a) e.
Proof. intro E;apply residue_eq. apply Zpower_mod;unfold Field.prime;lia. Qed.

Definition integer_uv y:=let yy:=y*y in let u:=121666*(yy-1) in u*(yy-u).
Lemma uv_field y : residue (integer_uv y)=(numerator(residue y)*denominator(residue y))%fp.
Proof. unfold integer_uv,denominator,numerator;repeat first [rewrite residue_mul|rewrite residue_sub];reflexivity. Qed.
Lemma test_field y :
 let v:=integer_uv y in let t:=v^exponent in
 residue (t*t*v)=test_value (numerator(residue y)) (denominator(residue y))
   (power (numerator(residue y)*denominator(residue y))%fp exponent).
Proof.
 cbv zeta;rewrite !residue_mul,pow_value by (vm_compute;discriminate || reflexivity);
 rewrite uv_field;unfold test_value;ring.
Qed.
