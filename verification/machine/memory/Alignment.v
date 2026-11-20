From Coq Require Import ZArith Lia Ring.
Open Scope Z_scope.
(* AND RSP,-64 clears exactly the six low address bits. This connects the
   relative pointer operation to integer x86 addresses at aligned placements. *)
Lemma and_rsp_64 n : Z.land n (-64)=n-n mod 64.
Proof.
 change (Z.land n (Z.lnot(Z.ones 6))=n-n mod 64).
 rewrite <-Z.ldiff_land,Z.ldiff_ones_r by lia.
 rewrite Z.shiftl_mul_pow2,Z.shiftr_div_pow2 by lia.
 pose proof(Z.div_mod n 64 ltac:(lia));change (n/64*64=n-n mod 64);lia.
Qed.
Theorem aligned_region_and origin offset : origin mod 64=0 ->
 Z.land (origin+offset)(-64)=origin+(offset-offset mod 64).
Proof.
 intro A;rewrite and_rsp_64,Z.add_mod by lia;rewrite A,Z.add_0_l,Z.mod_mod by lia;ring.
Qed.
