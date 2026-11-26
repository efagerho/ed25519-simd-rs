From Coq Require Import List ZArith Bool Lia.
From Curve25519.group Require Import DecompressionDigits.
From Coqprime.Z Require Import ZCAux.
From Coqprime.elliptic Require GZnZ.
From Curve25519 Require Import Field Radix51.
From Curve25519.group Require Import PrimeField Affine Decompression.
From Ed25519Simd.Decode Require Import Kernels Power.
From Curve25519 Require Import Radix51Digits DecompressionRadix51.
Local Open Scope Z_scope.

Definition value h := residue (pack h).
Definition mul k := apply_kernel k Multiply.
Definition sq k x := apply_kernel k Square x x.
Definition yy k y := mul k y y.
Definition uv k y := let h:=yy k y in mul k (u_digits h) (v_digits h).
Definition one := five 1 0 0 0 0.
Record output := Output { valid:bool; ox:field; oy:field; oz:field; ot:field }.
Definition finish k y sign t :=
 let h:=yy k y in let u:=u_digits h in let q:=mul k (sq k t) (uv k y) in
 let neg:=high_test q (-1) in
 let ok:=(high_test q 1 || high_test u 0 || neg)%bool in
 let x:=mul k u t in let x:=if neg then mul k x sqrt_limbs else x in
 let x:=if xorb (canonical_odd x) sign then finite(neg_digits x) else x in
 Output ok x y one (mul k x y).

Definition output_spec y sign o :=
 let x:=value(ox o) in let fy:=value y in
 split_field(ox o) /\ split_field(oy o) /\ split_field(oz o) /\ split_field(ot o) /\
 value(oy o)=fy /\ value(oz o)=1%fp /\ value(ot o)=(x*fy)%fp /\
 match valid o with true=>on_curve x fy /\ has_sign sign x
 | false=>forall a, ~on_curve a fy end.

Lemma mul_ok k a b : verified k Multiply=true -> split_field a -> split_field b ->
 bounded(mul k a b) /\ 2<=mul k a b 0%nat /\ value(mul k a b)=(value a*value b)%fp.
Proof.
 intros V A B; destruct (apply_ok _ _ _ _ V A B) as [D [Rep L]].
 split;[intros i I;specialize(D i I);change (0<=mul k a b i<=radix+2^16) in D;lia|].
 split;[apply L;reflexivity|]. apply congruent_value in Rep. unfold value;rewrite <-residue_mul;exact Rep.
Qed.
Local Lemma sq_ok k t : verified k Square=true -> squared t ->
 split_field(sq k t) /\ value(sq k t)=(value t*value t)%fp.
Proof.
 intros V T;destruct (apply_ok _ _ _ _ V T T) as [B [Rep _]].
 split;[apply squared_split;exact B|]. apply congruent_value in Rep. unfold value;rewrite <-residue_mul;exact Rep.
Qed.
Lemma setup_ok k y : verified k Multiply=true -> split_field y ->
 let h:=yy k y in let u:=u_digits h in let v:=v_digits h in
 bounded h /\ 2<=h 0%nat /\ bounded u /\ split_field(uv k y) /\
 value u=numerator(value y) /\ value(uv k y)=(numerator(value y)*denominator(value y))%fp.
Proof.
 intros M Y h u v. destruct(mul_ok _ _ _ M Y Y) as [H [L V]].
 destruct(scaled_bounds h H L) as [U D].
 destruct(mul_ok _ _ _ M (bounded_split _ U) (bounded_split _ D)) as [P [_ E]].
 assert (YY : represents (pack h) (pack y*pack y)).
 { apply congruent_value. rewrite residue_mul. exact V. }
 destruct (setup_field _ _ YY) as [Nu Dv].
 split; [exact H|]. split; [exact L|]. split; [exact U|]. split; [apply bounded_split;exact P|].
 split; [exact Nu|]. change (value (mul k u v) = (numerator(value y)*denominator(value y))%fp).
 change (value (mul k u v)=(value u*value v)%fp) in E. rewrite E.
 unfold u,v,value. now rewrite Nu,Dv.
Qed.

Local Lemma one_bound : split_field one.
Proof. intros [|[|[|[|i]]]] Lt; vm_compute;easy. Qed.

Theorem finish_correct k y sign t :
 verified k Multiply=true -> verified k Square=true -> split_field y -> squared t ->
 value t=power (value(uv k y)) exponent -> output_spec y sign (finish k y sign t).
Proof.
 intros M S Y T Pow.
 destruct (setup_ok _ _ M Y) as [H [L [U [UV [Nu E]]]]]. cbv zeta in H,L,U,UV,Nu,E.
 set (h:=yy k y) in *. set (u:=u_digits h) in *.
 destruct (sq_ok _ _ S T) as [B Tv].
 destruct (mul_ok _ _ _ M B UV) as [Q [Low Qv]]. set (q:=mul k (sq k t) (uv k y)) in *.
 set (fy:=value y) in *. rewrite E in Pow. rewrite Tv,Pow,E in Qv.
 assert (Qeq:value q=test_value (numerator fy) (denominator fy) (power (numerator fy*denominator fy)%fp exponent)).
 { rewrite Qv. unfold test_value. ring. }
 assert (Test:forall delta, -1<=delta<=1 ->
   (high_test q delta=true <-> value q=residue delta)).
 { intros delta D;rewrite high_test_correct by (assumption || apply positive_from_low; assumption). apply congruent_value. }
 assert (UT:high_test u 0=true <-> numerator fy=0%fp).
 { rewrite <-Nu. rewrite <- (congruent_value (pack u) 0). apply u_test_correct;auto. }
 assert (P:high_test q 1=true <-> value q=1%fp) by (apply Test;lia).
 assert (N:high_test q (-1)=true <-> value q=(0-1)%fp) by (apply Test;lia).
 destruct (mul_ok _ _ _ M (bounded_split _ U) (squared_split _ T)) as [X [_ Xv]].
 set (raw:=mul k u t) in *. rewrite Nu,Pow in Xv.
 destruct (mul_ok _ _ _ M (bounded_split _ X) sqrt_bound) as [IX [_ IXv]].
 set (adj:=if high_test q (-1) then mul k raw sqrt_limbs else raw).
 assert (AX:bounded adj) by (unfold adj;destruct(high_test q (-1));assumption).
 set (out:=if xorb (canonical_odd adj) sign then finite(neg_digits adj) else adj).
 destruct (neg_digits_ok _ AX) as [NX Ne];apply congruent_value in Ne. rewrite residue_opp in Ne.
 assert (OX:split_field out).
 { unfold out;destruct(xorb _ _);[intros i I;rewrite finite_at by exact I;apply NX,I|now apply bounded_split]. }
 assert (Ov:value out=signed_root sign (value adj)).
 { unfold out,signed_root. rewrite canonical_odd_ok by exact AX.
   change (Z.odd (pack adj mod prime)) with (parity (value adj)).
   destruct (parity (value adj)),sign;exact Ne || reflexivity. }
 destruct (mul_ok _ _ _ M OX Y) as [TO [_ Tvout]].
 unfold finish, output_spec. fold h u q raw adj out fy. cbn [valid ox oy oz ot].
 split;[exact OX|]. split;[exact Y|]. split;[exact one_bound|].
 split;[apply bounded_split;exact TO|]. split;[reflexivity|]. split;[reflexivity|].
 split;[exact Tvout|]. rewrite Ov.
 pose proof (decode_correct fy sign) as Correct. unfold decode in Correct. rewrite <-Qeq in Correct.
 assert (Root:value adj = (if high_test q (-1) then (numerator fy * power (numerator fy*denominator fy)%fp exponent * residue sqrt_m1)%fp
   else (numerator fy * power (numerator fy*denominator fy)%fp exponent)%fp)).
 { unfold adj. destruct (high_test q (-1)); [rewrite IXv,Xv|apply Xv];reflexivity. }
 rewrite Root. destruct (high_test q (-1)) eqn:Minus, (fp_eq_dec (value q) (0-1)%fp) as [NE|NE];
 cbn [orb] in Correct |- *.
 - rewrite Bool.orb_true_r. exact Correct.
 - exfalso;apply NE, N;reflexivity.
 - exfalso;apply N in NE;congruence.
 - rewrite Bool.orb_false_r. destruct (high_test q 1) eqn:Plus,(fp_eq_dec (value q) 1%fp) as [PE|PE].
   + exact Correct.
   + exfalso;apply PE,P;reflexivity.
   + exfalso;apply P in PE;congruence.
   + destruct (high_test u 0) eqn:Zero,(fp_eq_dec (numerator fy) 0%fp) as [ZE|ZE].
     * exact Correct.
     * exfalso;apply ZE,UT;reflexivity.
     * exfalso;apply UT in ZE;congruence.
     * exact Correct.
Qed.
