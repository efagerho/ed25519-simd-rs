From ProofArithmetic Require Import Interval Polynomial.
From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks Instructions WordBounds.
Require Import Program ScalarSpec ScalarMath Symbolic Product.
Import ListNotations. Open Scope Z_scope.
Definition code := fragment_code scalar_program 1.
Definition initial i := if Nat.eqb i 29 then I(C(B-1))(B-1)(B-1)else I(V i)0(W-1).
Definition no_loads (_:nat)(_:Z) := I(C 0)0 0.
Definition result := arun no_loads code initial.
Definition joinE x y scale cutoff :=
 Rem(Rem(Plus(Quot x cutoff)(Rem(Times y(C scale))W))W)B.
Definition chunkE first i := match i with
 | O=>Rem(V first)B
 | 1%nat=>joinE(V first)(V(first+1))(2^12)(2^52)
 | 2%nat=>joinE(V(first+1))(V(first+2))(2^24)(2^40)
 | 3%nat=>joinE(V(first+2))(V(first+3))(2^36)(2^28)
 | _=>Quot(V(first+3))(2^16) end.
Definition target i := if Nat.ltb i 18 then C 0 else
 if Nat.ltb i 23 then chunkE 0(i-18)else chunkE 4(i-23).
Definition unpack_check := check no_loads code initial &&
 forallb(fun i=>equal_expr(term(result i))(target i))(seq 0 28) &&
 forallb(fun i=>(0<=?lower(result i))&&(upper(result i)<=?Product.input_bound i))(seq 0 28).
Theorem unpack_checked : unpack_check=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque code.
Theorem unpack_correct load r :
 (forall b d,word64(load b d)) ->(forall i,word64(r i)) ->r 29%nat=B-1 ->
 Product.input_valid(run load code r) /\
 Product.pack(run load code r)18=number W[r 0%nat;r 1%nat;r 2%nat;r 3%nat] /\
 Product.pack(run load code r)23=number W[r 4%nat;r 5%nat;r 6%nat;r 7%nat].
Proof.
 intros LoadWords Words Mask;pose proof unpack_checked as Check;unfold unpack_check in Check.
 apply andb_true_iff in Check as[C Bounds];apply andb_true_iff in C as[Legal Targets].
 assert(Models:forall i,models r(initial i)(r i)).
 { intro i;unfold initial;destruct(Nat.eqb i 29)eqn:E.
   - apply Nat.eqb_eq in E;subst i;rewrite Mask;unfold models;cbn [val term lower upper ProofArithmetic.Interval.I enclosure lower_bound upper_bound];split;[reflexivity|lia].
   - unfold models;cbn [val term lower upper ProofArithmetic.Interval.I enclosure lower_bound upper_bound];split;[reflexivity|specialize(Words i);unfold word64,W in *;lia]. }
 pose proof(run_ok r no_loads load code initial r ltac:(intros b d I;change(In(b,d)[])in I;contradiction) Models Legal)as Model.
 change(forall i,models r(result i)(run load code r i))in Model.
 assert(Value:forall i,(i<28)%nat ->run load code r i=val r(target i)).
 { intros i I;rewrite forallb_forall in Targets;specialize(Targets i ltac:(apply in_seq;lia)).
   apply(equal_expr_sound r)in Targets;rewrite(proj1(Model i))in Targets;exact Targets. }
 split.
 - split.
   + intros i I;rewrite Value by lia;unfold target;assert(Nat.ltb i 18=true)by(apply Nat.ltb_lt;lia);rewrite H;reflexivity.
   + intro i;destruct(lt_dec i 28)as[I|I].
     * rewrite forallb_forall in Bounds;specialize(Bounds i ltac:(apply in_seq;lia)).
       apply andb_true_iff in Bounds as[A Z];apply Z.leb_le in A;apply Z.leb_le in Z.
       destruct(Model i)as[_ M];lia.
     * assert(Wrd:word64(run load code r i)).
       { apply run_words;assumption. }
       unfold Product.input_bound.
       assert((Nat.eqb i 22 || Nat.eqb i 27)=false)by(apply orb_false_iff;split;apply Nat.eqb_neq;lia).
       rewrite H;assert(Nat.leb 18 i && Nat.ltb i 28=false)by(apply andb_false_iff;right;apply Nat.ltb_ge;lia).
       rewrite H0;unfold word64,W in *;lia.
 - split;unfold Product.pack;cbn [seq map];repeat rewrite Value by lia;
   unfold target,chunkE,joinE;cbn [Nat.ltb Nat.sub Nat.add val];
   [change(number B(chunks (r 0%nat)(r 1%nat)(r 2%nat)(r 3%nat))=number W[r 0%nat;r 1%nat;r 2%nat;r 3%nat])|
    change(number B(chunks (r 4%nat)(r 5%nat)(r 6%nat)(r 7%nat))=number W[r 4%nat;r 5%nat;r 6%nat;r 7%nat])];
   apply chunks_correct;unfold W;apply Words.
Qed.
