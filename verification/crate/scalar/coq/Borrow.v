From Coq Require Import List ZArith Lia Ring.
From Machine Require Import isa.Instructions execution.WordBounds.
From Ed25519Simd.Scalar Require Import ScalarSpec ScalarMath.
Import ListNotations. Open Scope Z_scope.
Definition borrow d := (d mod W)/2^63.
Lemma borrow_correct d : -B<=d<B ->
 0<=borrow d<=1 /\ d=(d mod B)-B*borrow d.
Proof.
 intro D;unfold borrow;destruct(Z_lt_ge_dec d 0).
 - assert(E:d mod W=d+W).
   { symmetry;apply Z.mod_unique with(q:= -1);unfold B,W in *;[left;lia|ring]. }
   rewrite E;assert(H:(d+W)/2^63=1)by(symmetry;apply Z.div_unique with(r:=d+W-2^63);unfold B,W in *;[left;lia|ring]).
   rewrite H;assert(M:d mod B=d+B).
   { symmetry;apply Z.mod_unique with(q:= -1);unfold B in *;[left;lia|ring]. }
   rewrite M;split;[lia|ring].
 - rewrite Z.mod_small by(unfold B,W in *;lia).
   rewrite Z.div_small by(unfold B,W in *;lia).
   rewrite Z.mod_small by lia;split;[lia|ring].
Qed.
Lemma subtract_twice x y b : ((x-y)mod W-b)mod W=(x-y-b)mod W.
Proof.
 rewrite Zminus_mod by(pose proof W_positive;lia).
 rewrite Z.mod_mod by(pose proof W_positive;lia).
 symmetry;apply Zminus_mod;pose proof W_positive;lia.
Qed.
Definition select x d b := Z.lxor(Z.land(Z.lxor x(d mod B))((0-b)mod W))(d mod B).
Lemma select_correct x d b : word64 x ->(b=0 \/ b=1) ->
 select x d b=if b=?0 then d mod B else x.
Proof.
 intros X [-> | ->];unfold select;cbn [Z.eqb].
 - replace((0-0)mod W)with 0 by reflexivity;rewrite Z.land_0_r,Z.lxor_0_l;reflexivity.
 - replace((0-1)mod W)with(Z.ones 64)by reflexivity.
   rewrite Z.land_ones by lia.
   rewrite Z.mod_small.
   + rewrite Z.lxor_assoc,Z.lxor_nilpotent,Z.lxor_0_r;reflexivity.
   + apply xor_word;[exact X|].
     pose proof(Z.mod_pos_bound d B B_positive);unfold word64,B,W in *;lia.
Qed.
Definition modulus_digit i := match i with O=>l0 | 1%nat=>l1 | 2%nat=>l2 | 3%nat=>0 | _=>l4 end.
Definition diff x i b := x i-modulus_digit i-b.
Fixpoint borrow_at x n := match n with O=>0 | S i=>borrow(diff x i(borrow_at x i))end.
Definition candidate x i := diff x i(borrow_at x i)mod B.
Definition low := low_digits B.
Lemma modulus_digits_bounded i : 0<=modulus_digit i<B.
Proof. destruct i as[|[|[|[|i]]]];unfold modulus_digit,l0,l1,l2,l4,B;lia. Qed.
Lemma borrow_chain x n : (forall i,(i<n)%nat->0<=x i<B) ->
 0<=borrow_at x n<=1 /\
 low x n-low modulus_digit n=low(candidate x)n-B^Z.of_nat n*borrow_at x n.
Proof.
 intro X. apply subtraction_chain; [reflexivity|].
 intros i I Bound. specialize (X i I). pose proof (modulus_digits_bounded i).
 apply (borrow_correct (diff x i (borrow_at x i))). unfold diff; lia.
Qed.
Lemma low_pack x : low x 5=number B(map x(seq 0 5)).
Proof.
 change(0+1*x 0%nat+B^1*x 1%nat+B^2*x 2%nat+B^3*x 3%nat+B^4*x 4%nat=
 x 0%nat+B*(x 1%nat+B*(x 2%nat+B*(x 3%nat+B*(x 4%nat+B*0)))));ring.
Qed.
Lemma canonical_digits x : (forall i,(i<5)%nat->0<=x i<B) ->
 0<=low x 5<2*L ->
 let y:=fun i=>select(x i)(diff x i(borrow_at x i))(borrow_at x 5)in
 low y 5=low x 5 mod L /\(forall i,(i<5)%nat->0<=y i<B).
Proof.
 intros X U y;destruct(borrow_chain x 5 X)as[Borrow Eq].
 assert(Mod:low modulus_digit 5=L)by(vm_compute;reflexivity).
 rewrite Mod in Eq.
 assert(C:0<=low(candidate x)5<R).
 { rewrite low_pack;apply number_bound;[apply B_positive|].
   apply Forall_forall;intros z I;apply in_map_iff in I as[i [<- I]];apply Z.mod_pos_bound,B_positive. }
 assert(Choice:borrow_at x 5=0 \/ borrow_at x 5=1)by lia.
 assert(Y:forall i,(i<5)%nat->y i=if borrow_at x 5=?0 then candidate x i else x i).
 { intros i I;unfold y;apply select_correct;[specialize(X i I);unfold word64,B in *;lia|exact Choice]. }
 assert(Values:low y 5=if borrow_at x 5=?0 then low(candidate x)5 else low x 5).
 { rewrite !low_pack;cbn [seq map number];repeat rewrite Y by lia;
   destruct(borrow_at x 5=?0);reflexivity. }
 split.
 - rewrite Values. eapply conditional_subtraction; eauto using L_positive.
 - intros i I;rewrite Y by exact I;destruct(borrow_at x 5=?0);[apply Z.mod_pos_bound,B_positive|apply X,I].
Qed.
