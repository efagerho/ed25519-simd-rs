From Coq Require Import List ZArith Bool Lia Ring.
From Machine Require Import Blocks Instructions WordBounds Dependencies.
Require Import Program ScalarSpec ScalarMath Product Unpack Reduction Montgomery Borrow Finish.
Import ListNotations. Open Scope Z_scope.
Definition prepare r i := if Nat.eqb i 23 then 0 else match constants i with Some c=>c | None=>r i end.
Definition calculate load r :=
 let u:=run load Unpack.code(put r 29%nat(B-1))in
 let p:=multiply 5 load u in
 let m:=reduce 5 load(prepare p)in
 run load Finish.code(run load normalize_code m).
Lemma prepare_constants r : constants_ok(prepare r).
Proof. intros i c C;unfold prepare;destruct(Nat.eqb i 23)eqn:E;[apply Nat.eqb_eq in E;subst;discriminate|now rewrite C]. Qed.
Lemma prepare_words r : (forall i,word64(r i))->forall i,word64(prepare r i).
Proof.
 intros Words i;unfold prepare;destruct(Nat.eqb i 23);[unfold word64;lia|].
 unfold constants;do 32(destruct i as[|i];[cbn;try apply Words;unfold word64,B,l0,l1,l2,l4,factor;lia|]);apply Words.
Qed.
Lemma prepare_bound r : (forall i,(i<28)%nat->0<=r i<10*B)->bounded_state 0(prepare r).
Proof.
 intros Bound i I;unfold prepare;destruct(Nat.eqb i 23);[unfold bound,B in *;lia|].
 assert(C:constants i=None)by(unfold constants;do 26(destruct i as[|i];[reflexivity|]);lia).
 rewrite C;specialize(Bound i ltac:(lia));unfold bound,B in *;lia.
Qed.
Lemma prepare_total r : remaining 0(prepare r)=total r.
Proof. unfold remaining,total;cbn [seq map number prepare constants Nat.eqb Nat.sub Nat.add];ring. Qed.
Local Opaque constant0 constant1 product_code.
Lemma multiply_words n load r : (forall b d,word64(load b d))->(forall i,word64(r i))->
 forall i,word64(multiply n load r i).
Proof.
 intros Loads Words;induction n;cbn [multiply];[exact Words|].
 apply run_words;[exact Loads|];intro i;unfold with_constants,put.
 assert(Mod:forall x,word64(x mod B)).
 { intro x;pose proof(Z.mod_pos_bound x B B_positive);unfold word64,B in *;lia. }
 destruct(Nat.eqb 29 i);[exact(Mod(multiplier1/B^Z.of_nat n))|].
 destruct(Nat.eqb 28 i);[exact(Mod(multiplier0/B^Z.of_nat n))|apply IHn].
Qed.
Lemma reduce_words n load r : (forall b d,word64(load b d))->(forall i,word64(r i))->
 forall i,word64(reduce n load r i).
Proof. intros Loads Words;induction n;cbn [reduce];[exact Words|apply run_words;assumption]. Qed.
Lemma normalize_constants load r : constants_ok r ->constants_ok(run load normalize_code r).
Proof.
 intros C i c I;rewrite(untouched load normalize_code r i);[apply C,I|].
 unfold constants in I;do 32(destruct i as[|i];[try discriminate;vm_compute;reflexivity|]);discriminate.
Qed.
Lemma half_bound r first : (forall i,word64(r i))->
 0<=number W[r first;r(first+1)%nat;r(first+2)%nat;r(first+3)%nat]<2^256.
Proof.
 intro Words;change(0<=number W[r first;r(first+1)%nat;r(first+2)%nat;r(first+3)%nat]<W^Z.of_nat(length[r first;r(first+1)%nat;r(first+2)%nat;r(first+3)%nat])).
 apply number_bound;[apply W_positive|repeat constructor;apply Words].
Qed.
Lemma top_bound r : (forall i,(i<4)%nat->0<=r i<B) ->0<=r 4%nat ->
 0<=pack r 0<2*L ->0<=r 4%nat<B.
Proof.
 intros Limbs Top Range.
 pose proof(Limbs 0%nat ltac:(lia));pose proof(Limbs 1%nat ltac:(lia));
 pose proof(Limbs 2%nat ltac:(lia));pose proof(Limbs 3%nat ltac:(lia)).
 unfold pack in Range;cbn [seq map number Nat.add]in Range;unfold B,L in *;nia.
Qed.
Local Opaque run Unpack.code multiply prepare reduce normalize_code Finish.code.
Theorem calculate_correct load r : (forall b d,word64(load b d))->(forall i,word64(r i))->
 pack(calculate load r)0=number W(map r(seq 0 8))mod L /\
 (forall i,(i<5)%nat->0<=calculate load r i<B).
Proof.
 intros Loads Words;set(start:=put r 29%nat(B-1)).
 assert(SWords:forall i,word64(start i)).
 { intro i;unfold start,put;destruct(Nat.eqb 29 i);[unfold word64,B;lia|apply Words]. }
 destruct(unpack_correct load start Loads SWords eq_refl)as[Input [A D]].
 set(u:=run load Unpack.code start)in *;set(p:=multiply 5 load u).
 assert(UWords:forall i,word64(u i))by(apply run_words;assumption).
 assert(PWords:forall i,word64(p i))by(apply multiply_words;assumption).
 destruct(product_correct load u Input)as[Product PB];fold p in Product,PB.
 destruct(reduce_correct 5 load(prepare p)ltac:(lia)Loads(prepare_words p PWords)
 (prepare_constants p)(prepare_bound p PB))as[Const [Bound [q [Q Eq]]]].
 rewrite prepare_total,Product in Eq.
 set(m:=reduce 5 load(prepare p))in *.
 assert(MWords:forall i,word64(m i))by(apply reduce_words;[exact Loads|apply prepare_words,PWords]).
 destruct(normalize_correct load m MWords Const Bound)as[Normal [Limbs Top]].
 set(v:=run load normalize_code m)in *.
 change(R*remaining 5 m=pack u 18*multiplier0+pack u 23*multiplier1+q*L)in Eq.
 rewrite <-Normal in Eq;change(0<=q<R)in Q.
 assert(AB:0<=pack u 18<2^256)by(rewrite A;apply half_bound,SWords).
 assert(DB:0<=pack u 23<2^256)by(rewrite D;apply(half_bound start 4 SWords)).
 assert(Range:0<=pack v 0<2*L)by(exact(montgomery_range(pack u 18)(pack u 23)(pack v 0)q AB DB Q Eq)).
 assert(VBounds:forall i,(i<5)%nat->0<=v i<B).
 { intros i I;destruct(lt_dec i 4);[apply Limbs;lia|assert(i=4)%nat by lia;subst].
   apply top_bound;assumption. }
 destruct(finish_correct load v(normalize_constants load m Const)VBounds Range)as[Value Bounds].
 change(pack(run load Finish.code v)0=number W(map r(seq 0 8))mod L /\ (forall i,(i<5)%nat->0<=run load Finish.code v i<B)).
 split;[|exact Bounds]. rewrite Value,(montgomery_residue _ _ _ _ Eq),A,D.
 f_equal;unfold start,put;cbn [seq map number Nat.eqb Nat.add];unfold W;ring.
Qed.
