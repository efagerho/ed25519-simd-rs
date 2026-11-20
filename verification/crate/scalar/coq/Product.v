From ProofArithmetic Require Import Interval Polynomial.
From Coq Require Import List ZArith Bool Lia Ring.
From Machine Require Import Blocks Instructions WordBounds.
From Ed25519Simd.Scalar Require Import Program ScalarSpec Symbolic.
Import ListNotations. Open Scope Z_scope.

Definition multiplier0 := R mod L.
Definition multiplier1 := (2^256*R) mod L.
Definition constant0 i := multiplier0 / B^Z.of_nat i mod B.
Definition constant1 i := multiplier1 / B^Z.of_nat i mod B.
Definition product_code i := fragment_code scalar_program (2+i)%nat.
Definition pack r first := number B(map(fun i=>r(first+i)%nat)(seq 0 5)).
Definition packE s first := numberE B(map(fun i=>s(first+i)%nat)(seq 0 5)).
Definition total r := number B(map(fun i=>r i+B*r(9+i)%nat)(seq 0 9)).
Definition totalE s := numberE B(map(fun i=>Plus(s i)(Times(C B)(s(9+i)%nat)))(seq 0 9)).
Definition input_bound i := if (Nat.eqb i 22 || Nat.eqb i 27)then 2^48-1
 else if Nat.leb 18 i && Nat.ltb i 28 then B-1 else W-1.
Definition initial i := if Nat.ltb i 18 then I(C 0)0 0 else I(V i)0(input_bound i).
Definition input_valid r := (forall i,(i<18)%nat->r i=0) /\
 (forall i,0<=r i<=input_bound i).
Definition with_constants r i := put(put r 28%nat(constant0 i))29%nat(constant1 i).
Definition with_symbolic_constants s i := put(put s 28%nat
 (I(C(constant0 i))(constant0 i)(constant0 i)))29%nat
 (I(C(constant1 i))(constant1 i)(constant1 i)).
Definition no_loads (_:nat)(_:Z) := I(C 0)0 0.
Fixpoint multiply n load r := match n with O=>r | S i=>
 run load(product_code i)(with_constants(multiply i load r)i) end.
Fixpoint result n := match n with O=>initial | S i=>
 arun no_loads(product_code i)(with_symbolic_constants(result i)i) end.
Fixpoint checked n := match n with O=>true | S i=>checked i &&
 check no_loads(product_code i)(with_symbolic_constants(result i)i) end.
Definition target := Plus(Times(packE V 18)(C multiplier0))(Times(packE V 23)(C multiplier1)).

Lemma input_models r : input_valid r ->forall i,models r(initial i)(r i).
Proof.
 intros[Zero Bound]i;unfold initial;destruct(Nat.ltb i 18)eqn:E;
 unfold models;cbn [term lower upper val ProofArithmetic.Interval.I enclosure lower_bound upper_bound].
 - apply Nat.ltb_lt in E;rewrite(Zero i E);split;[reflexivity|lia].
 - split;[reflexivity|apply Bound].
Qed.
Lemma code_loads i : (i<5)%nat ->loads_of(product_code i)=[].
Proof. intro H;do 5(destruct i as[|i];[vm_compute;reflexivity|]);lia. Qed.
Local Opaque constant0 constant1 product_code.
Theorem multiply_models env load r n : (n<=5)%nat ->
 (forall i,models env(initial i)(r i)) ->checked n=true ->
 forall i,models env(result n i)(multiply n load r i).
Proof.
 induction n as[|n IH];intros N Model Check;[exact Model|].
 cbn [checked]in Check;apply andb_true_iff in Check as[C D].
 cbn [result multiply];apply run_ok;[| |exact D].
 - intros b disp Member;rewrite code_loads in Member by lia;contradiction.
 - intro i;unfold with_constants,with_symbolic_constants,put.
   destruct(Nat.eqb 29 i),(Nat.eqb 28 i);try(unfold models;cbn;split;[reflexivity|lia]).
   apply IH;auto;lia.
Qed.
Local Transparent constant0 constant1 product_code.
Definition product_check := checked 5 &&
 equal_expr(totalE(fun i=>term(result 5 i)))target &&
 forallb(fun i=>(0<=?lower(result 5 i))&&(upper(result 5 i)<?10*B))(seq 0 28).
Theorem product_checked : product_check=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque checked result.
Theorem product_correct load r : input_valid r ->
 total(multiply 5 load r)=pack r 18*multiplier0+pack r 23*multiplier1 /\
 (forall i,(i<28)%nat ->0<=multiply 5 load r i<10*B).
Proof.
 intro Input;pose proof product_checked as Check;unfold product_check in Check.
 apply andb_true_iff in Check as[CE Bounds];apply andb_true_iff in CE as[C E].
 pose proof(multiply_models r load r 5 ltac:(lia)(input_models _ Input)C)as Model.
 split.
 - apply(equal_expr_sound r)in E.
   unfold totalE,target,packE in E;rewrite !numberE_sound in E.
   cbn [val]in E;rewrite !numberE_sound in E.
   unfold total,pack.
   cbn [seq map number val]in E|-*.
   repeat rewrite (fun i=>proj1(Model i))in E.
   exact E.
 - intros i I;rewrite forallb_forall in Bounds;specialize(Bounds i ltac:(apply in_seq;lia)).
   apply andb_true_iff in Bounds as[A B0];apply Z.leb_le in A;apply Z.ltb_lt in B0.
   destruct(Model i)as[_ H];lia.
Qed.
