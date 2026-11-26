From ProofArithmetic Require Import Radix.
From Coq Require Import ZArith List Lia.
From Machine Require Import isa.X86 isa.Arithmetic.
From Curve25519 Require Import Scalar SignedRadix16.
From Ed25519Simd Require Import Radix16Output.
From Ed25519Simd.SignatureScalar Require Import Inputs.
Local Open Scope Z_scope.

Definition l0 := 0x5812631a5cf5d3ed.
Definition l1 := 0x14def9dea2f79cd6.
Definition l3 := 0x1000000000000000.
Definition below a b c d p q z :=
 (((((a <? p) && (b =? q)) || (b <? q)) && (c =? 0)) && (d =? z) || (d <? z))%bool.
Lemma below_correct a b c d : 0<=a<Q -> 0<=b<Q -> 0<=c<Q -> 0<=d<Q ->
 below a b c d l0 l1 l3 = (four_words a b c d <? L).
Proof.
 intros A B C D. unfold below.
 replace (four_words a b c d) with ((a+Q*b)+Q^2*c+Q^3*d)
   by (unfold four_words; ring).
 change L with ((l0+Q*l1)+Q^2*0+Q^3*l3).
 rewrite (compare_digit (Q^3)), (compare_digit (Q^2)), (compare_digit Q)
   by (unfold Q,l0,l1 in *; lia).
 replace (c <? 0) with false by (symmetry;apply Z.ltb_ge;lia).
 now rewrite Bool.orb_false_r.
Qed.

Definition B := 0x8888888888888888.
Definition biased a := vpaddq a B.
Definition adjust a previous input :=
 if previous <? input then vpaddq (biased a) 1 else biased a.
Definition carry out a := Z.b2z (out <? a).
Lemma add_word a k : 0<=a<Q -> 0<=k<=1 ->
 let w:=(a+B+k) mod Q in 0<=w<Q /\ a+B+k=w+Q*carry w a.
Proof.
 intros A K w;split;[apply Z.mod_pos_bound;unfold Q;lia|].
 unfold carry,w;destruct (Z_lt_ge_dec (a+B+k) Q).
 - rewrite Z.mod_small by (unfold B,Q in *;lia).
   rewrite (proj2 (Z.ltb_ge _ _)) by (unfold B;lia);cbn [Z.b2z];ring.
 - replace ((a+B+k) mod Q) with (a+B+k-Q) by
    (apply Z.mod_unique with (q:=1);[left;unfold B,Q in *;lia|ring]).
   rewrite (proj2 (Z.ltb_lt _ _)) by (unfold B,Q in *;lia);cbn [Z.b2z];ring.
Qed.
Lemma biased_mod a : biased a=(a+B+0) mod Q.
Proof. unfold biased,vpaddq,low64,Q;rewrite Z.land_ones,Z.add_0_r by lia;reflexivity. Qed.
Lemma adjust_mod a p x : adjust a p x=(a+B+carry p x) mod Q.
Proof.
 unfold adjust,carry;rewrite biased_mod;destruct (p<?x);[|reflexivity].
 unfold vpaddq,low64,Q;rewrite Z.land_ones,Z.add_mod_idemp_l,Z.add_0_r by lia;reflexivity.
Qed.
Definition output_word a b c d i :=
 let w:=biased a in let x:=adjust b w a in let y:=adjust c x b in
 match i with O=>w | S O=>x | S(S O)=>y | _=>adjust d y c end.

Lemma biased_chunk a b c d i : (i<4)%nat ->
 0<=a<Q -> 0<=b<Q -> 0<=c<Q -> 0<=d<Q ->
 output_word a b c d i=chunk (four_words a b c d+bias 64) i.
Proof.
 intros I A E C D. set (w:=biased a);set (x:=adjust b w a);
 set (y:=adjust c x b);set (z:=adjust d y c).
 assert (Bit:forall p u,0<=carry p u<=1) by (intros;unfold carry;destruct (_<?_);cbv;intuition discriminate).
 pose proof (add_word a 0 A ltac:(lia)) as H0.
 pose proof (add_word b (carry w a) E (Bit _ _)) as H1.
 pose proof (add_word c (carry x b) C (Bit _ _)) as H2.
 pose proof (add_word d (carry y c) D (Bit _ _)) as H3.
 cbv zeta in H0,H1,H2,H3.
 rewrite <-biased_mod in H0; rewrite <-adjust_mod in H1,H2,H3.
 fold w in H0;fold x in H1;fold y in H2;fold z in H3.
 assert (Total:four_words a b c d+bias 64=
   four_words w x y z + 2^256*carry z d).
 { change (bias 64) with (four_words B B B B).
   unfold four_words,Q in *;lia. }
 rewrite Total;unfold output_word;fold w x y z.
 assert (Get:forall n v low high i, 0<=low<2^(64*Z.of_nat i) -> 0<=v<Q ->
   n=low+(v+high*Q)*2^(64*Z.of_nat i) -> v=chunk n i).
 { intros n v low high idx Lo V ->;unfold chunk;rewrite Z.div_add by (apply Z.pow_nonzero;lia).
   rewrite Z.div_small by exact Lo;rewrite Z.add_0_l;fold Q;rewrite Z.mod_add by (unfold Q;lia).
   now rewrite Z.mod_small. }
 destruct i as [|[|[|[|i]]]];try lia.
 - apply (Get _ _ 0 (x+Q*(y+Q*(z+Q*carry z d))));unfold four_words,Q in *;lia.
 - apply (Get _ _ w (y+Q*(z+Q*carry z d)));unfold four_words,Q in *;lia.
 - apply (Get _ _ (w+Q*x) (z+Q*carry z d));unfold four_words,Q in *;lia.
 - apply (Get _ _ (w+Q*(x+Q*y)) (carry z d));unfold four_words,Q in *;lia.
Qed.
Lemma rejected_chunk i : (i<4)%nat -> B=chunk (0+bias 64) i.
Proof. intros I;destruct i as [|[|[|[|i]]]];try lia;reflexivity. Qed.
Lemma zero_digit k : (k<64)%nat -> digit 0 k=0.
Proof.
 intro K;assert(H:forallb (fun j=>digit 0 j=?0) (seq 0 64)=true) by (vm_compute;reflexivity).
 apply (proj1 (forallb_forall _ _)) with (x:=k) in H;[now apply Z.eqb_eq|apply in_seq;lia].
Qed.
