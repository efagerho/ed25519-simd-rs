From Curve25519.group Require Import PrimeField Affine Decompression.
Local Open Scope fp_scope.

(* The three equality tests classify the possible square roots independently
   of which encoded sign is requested. *)
Theorem root_criterion y :
 let u:=numerator y in let v:=denominator y in
 let q:=test_value u v (power (u*v) exponent) in
 (q=1 \/ u=0 \/ q=0-1) <-> exists x,on_curve x y.
Proof.
 cbv zeta;pose proof(decode_correct y false) as D.
 unfold decode in D;cbv zeta in D;set (u:=numerator y) in *;set (v:=denominator y) in *.
 set (t:=power (u*v) exponent) in *;set (q:=test_value u v t) in *.
 destruct(fp_eq_dec q (0-1)),(fp_eq_dec q 1),(fp_eq_dec u 0);
   try (split;[intros _;eexists;exact (proj1 D)|tauto]).
 split;[tauto|intros [x X];exfalso;exact (D x X)].
Qed.
