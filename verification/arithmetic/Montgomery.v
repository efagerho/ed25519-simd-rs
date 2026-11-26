From Coq Require Import ZArith Lia Ring.
Local Open Scope Z_scope.

(* The low digit of x + q*m vanishes when factor is -1/m modulo base. *)
Definition cancellation_digit base factor x := ((x mod base)*factor) mod base.

Lemma low_cancel base m factor x :
 0 < base -> (factor*m+1) mod base = 0 ->
 (x + cancellation_digit base factor x*m) mod base = 0.
Proof.
 intros B Inv. unfold cancellation_digit.
 assert (Nonzero : base <> 0) by lia.
 apply (proj2 (Z.mod_divide _ base Nonzero)).
 apply (proj1 (Z.mod_divide _ base Nonzero)) in Inv as [k Inv].
 exists (x*k-(x/base)*factor*m-((x mod base*factor)/base)*m).
 set (t := (x mod base*factor)/base).
 rewrite (Z.mod_eq (x mod base*factor) base) by lia. fold t.
 rewrite (Z.mod_eq x base) by lia.
 replace (x+((x-base*(x/base))*factor-base*t)*m)
   with (x*(factor*m+1)-base*((x/base)*factor*m+t*m)) by ring.
 rewrite Inv; ring.
Qed.

Lemma cancelled_carry base x addend :
 0 < base -> (x+addend) mod base = 0 ->
 base*((x+base-1)/base) = x + addend mod base.
Proof.
 intros B Cancel.
 pose proof (Z.div_mod x base ltac:(lia)).
 pose proof (Z.div_mod addend base ltac:(lia)).
 pose proof (Z.div_mod (x+addend) base ltac:(lia)).
 pose proof (Z.mod_pos_bound x base B).
 pose proof (Z.mod_pos_bound addend base B).
 assert (E : (x+base-1)/base = x/base + (if x mod base =? 0 then 0 else 1)).
 { symmetry. apply Z.div_unique with
     (r:=if x mod base =? 0 then base-1 else x mod base-1);
   destruct (Z.eqb_spec (x mod base) 0); try left; nia. }
 rewrite E. assert (D : x mod base + addend mod base =
     base*((x+addend)/base - x/base - addend/base)) by nia.
 assert (R : 0 <= (x+addend)/base - x/base - addend/base <= 1) by nia.
 set (c := (x+addend)/base - x/base - addend/base) in D,R.
 assert (c=0 \/ c=1) as [C|C] by lia; rewrite C in D;
   destruct (Z.eqb_spec (x mod base) 0); nia.
Qed.

(* R has a checked inverse modulo m. The two inputs have weights 1 and w. *)
Lemma reduce_pair m R inv witness w a b u q :
 0 < m -> R*inv = 1+m*witness ->
 R*u = a*(R mod m)+b*((w*R) mod m)+q*m ->
 u mod m = (a+w*b) mod m.
Proof.
 intros M Inverse Eq. set (h:=a+w*b).
 set (k:=q-a*(R/m)-b*((w*R)/m)).
 assert (E : R*(u-h) = m*k).
 { unfold h,k. rewrite (Z.mod_eq R m), (Z.mod_eq (w*R) m) in Eq by lia. nia. }
 assert (F : u = h + (k*inv-(u-h)*witness)*m).
 {
   assert (D : (u-h)*(1+m*witness) = m*k*inv)
     by (rewrite <-Inverse, <-E; ring).
   nia. }
 rewrite F; apply Z.mod_add; lia.
Qed.
