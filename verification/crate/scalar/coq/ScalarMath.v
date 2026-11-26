From Coq Require Import List ZArith Lia Ring.
From Ed25519Simd.Scalar Require Import ScalarSpec.
Import ListNotations. Open Scope Z_scope.
Lemma mod_word_B x : (x mod W)mod B=x mod B.
Proof.
 symmetry;apply Znumtheory.Zmod_div_mod;[apply B_positive|apply W_positive|].
 exists 4096;vm_compute;reflexivity.
Qed.
Definition join x y scale cutoff := ((x/cutoff+(y*scale mod W))mod W)mod B.
Lemma join_exact x y scale high cutoff :
 0<=x<W ->0<scale ->0<high ->0<cutoff ->scale*high=B ->cutoff*scale=W ->
 join x y scale cutoff=x/cutoff+(y mod high)*scale.
Proof.
 intros X S H C B0 W0;unfold join;rewrite mod_word_B.
 rewrite Z.add_mod by(pose proof B_positive;lia).
 rewrite mod_word_B;rewrite <-Z.add_mod by(pose proof B_positive;lia).
 assert(Q:0<=x/cutoff<scale).
 { split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia. }
 pose proof(Z.mod_pos_bound y high H).
 pose proof(Z.div_mod y high ltac:(lia)).
 symmetry;apply Z.mod_unique with(q:=y/high);[left;nia|nia].
Qed.
Definition chunks x0 x1 x2 x3 :=
 [x0 mod B;join x0 x1 (2^12)(2^52);join x1 x2(2^24)(2^40);
  join x2 x3(2^36)(2^28);x3/2^16].
Lemma chunks_correct x0 x1 x2 x3 :
 0<=x0<W ->0<=x1<W ->0<=x2<W ->0<=x3<W ->
 number B(chunks x0 x1 x2 x3)=number W[x0;x1;x2;x3].
Proof.
 intros A D E F;unfold chunks.
 rewrite(join_exact x0 x1 (2^12)(2^40)(2^52))by(unfold B,W in *;lia).
 rewrite(join_exact x1 x2 (2^24)(2^28)(2^40))by(unfold B,W in *;lia).
 rewrite(join_exact x2 x3 (2^36)(2^16)(2^28))by(unfold B,W in *;lia).
 pose proof(Z.div_mod x0 B ltac:(pose proof B_positive;lia)).
 pose proof(Z.div_mod x1 (2^40)ltac:(lia)).
 pose proof(Z.div_mod x2 (2^28)ltac:(lia)).
 pose proof(Z.div_mod x3 (2^16)ltac:(lia)).
 cbn [number];unfold B,W in *;lia.
Qed.
