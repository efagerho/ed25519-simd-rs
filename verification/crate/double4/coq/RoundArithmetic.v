From Coq Require Import List ZArith Bool Lia Ring.
From Machine Require Import execution.Blocks isa.Instructions execution.WordBounds execution.Dependencies.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Curve25519 Require Import FieldPolynomial.
From Ed25519Simd.Double4 Require Import Program Double4ABI Kernels KernelInterface Round.
Import ListNotations. Open Scope Z_scope.
Local Opaque code.
Definition operand_fields k x y := match k with
 | AddReduce | SquarePair=>loose x /\ loose y
 | SubtractReduce=>squared x /\ squared y
 | _=>split_field x /\ split_field y end.
Lemma fields_operands k s : operand_fields k (rfield s 0) (rfield s 5) -> constants s ->
 (match k with SubtractReduce=>registers s 30%nat=bias 0 /\ registers s 31%nat=bias 1 | _=>True end) ->
 operands k (registers s).
Proof.
 intros Input [C Mask] Bias;unfold operands;split;[|split;[|auto]].
 - destruct k;cbn [operand_fields] in Input;destruct Input as [X Y];
   try (destruct X as[X XL];destruct Y as[Y YL]);
   intros i I;do 10(destruct i as[|i];
     [first [apply X;lia|apply Y;lia]|]);lia.
 - destruct k;try exact I. destruct Input as [[X XL] [Y YL]];split;assumption.
Qed.
Lemma call_words j k base s : lane_words s -> lane_words (call j k base s).
Proof. rewrite <-call_is_effect;apply lane_effect_words;reflexivity. Qed.
Lemma call_correct j k base s m start :
 lane_words s -> operand_fields k (rfield s 0) (rfield s 5) -> constants s ->
 (match k with SubtractReduce=>registers s 30%nat=bias 0 /\ registers s 31%nat=bias 1 | _=>True end) ->
 right_ok k m ->
 (forall i,(i<right_count k)%nat -> cells s (offset base (64*Z.of_nat i))=m i) ->
 In start (output_starts k) ->
 field_bound (fun i=>bound k (start+i)%nat) (rfield (call j k base s) start) /\
 represents (limbs (rfield (call j k base s) start)) (val (env (registers s) m) (target k start)).
Proof.
 intros [W _] Input Const Bias Right Mem Start.
 unfold rfield,get;rewrite call_registers.
 eapply run_correct;try eassumption;[now apply fields_operands|].
 intros i I;destruct k;cbn [load_base right_count] in *;
 try lia.
 all: cbn [lane_load];try (rewrite Nat.eqb_refl;cbn [find fst snd]);try apply Mem;auto.
Qed.
Definition target_value k r m start := match k with
 | AddReduce=>pack r 0+pack r 5
 | SquarePair=>pack r start*pack r start
 | MultiplyPair | MultiplySingle=>pack r start*pack m 0
 | SubtractReduce=>let a:=pack m 0 in let b:=pack m 5 in
   if Nat.eqb start 0 then pack r 5-(a+b) else
   if Nat.eqb start 5 then -(a+b) else
   if Nat.eqb start 10 then b-a else (b-a)-2*pack r 0 end.
Local Opaque packE.
Lemma target_value_ok k r m start : val (env r m) (target k start)=target_value k r m start.
Proof.
 destruct k;unfold target,target_value;repeat match goal with |- context[if ?b then _ else _]=>destruct b eqn:? end;
 cbn [val minus];rewrite ?pack_env_reg,?pack_env_mem;ring.
Qed.
Lemma call_add j s : lane_words s -> constants s -> loose(rfield s 0) -> loose(rfield s 5) ->
 ready(rfield(call j AddReduce (scratch,0) s)10) /\
 represents (limbs(rfield(call j AddReduce (scratch,0) s)10)) (limbs(rfield s 0)+limbs(rfield s 5)).
Proof.
 intros W C X Y.
 pose proof(call_correct j AddReduce (scratch,0) s (fun _=>0) 10 W (conj X Y) C I
   ltac:(intros i H;cbn [right_count] in H;lia)
   ltac:(intros i H;cbn [right_count] in H;lia) ltac:(cbn [output_starts In];auto)) as [B V].
 split;[exact B|rewrite target_value_ok in V;exact V].
Qed.
Lemma call_square j s start : lane_words s -> constants s -> loose(rfield s 0) -> loose(rfield s 5) ->
 (start=0%nat \/ start=5%nat) ->
 squared(rfield(call j SquarePair (scratch,0) s)start) /\
 represents (limbs(rfield(call j SquarePair (scratch,0) s)start)) (limbs(rfield s start)*limbs(rfield s start)).
Proof.
 intros W C X Y Start.
 pose proof(call_correct j SquarePair (scratch,0) s (fun _=>0) start W (conj X Y) C I
   ltac:(intros i H;cbn [right_count] in H;lia)
   ltac:(intros i H;cbn [right_count] in H;lia)
   ltac:(destruct Start as[-> | ->];cbn [output_starts In];auto)) as [B V].
 split;[|rewrite target_value_ok in V;exact V].
 destruct Start as[-> | ->];intros i I;do 5(destruct i as[|i];[apply B;lia|]);lia.
Qed.
Lemma call_subtract j s start : lane_words s -> constants s ->
 squared(rfield s 0) -> squared(rfield s 5) ->
 squared(field s scratch 0) -> squared(field s scratch 5) ->
 registers s 30%nat=bias 0 -> registers s 31%nat=bias 1 ->
 In start [0%nat;5%nat;10%nat;15%nat] ->
 ready(rfield(call j SubtractReduce (scratch,0) s)start) /\
 represents (limbs(rfield(call j SubtractReduce (scratch,0) s)start))
 (target_value SubtractReduce (registers s) (fun i=>cells s(scratch,64*Z.of_nat i)) start).
Proof.
 intros W C X Y A B Bias0 Bias1 Start.
 pose proof(call_correct j SubtractReduce (scratch,0) s (fun i=>cells s(scratch,64*Z.of_nat i)) start
 W (conj X Y) C (conj Bias0 Bias1) ltac:(
 intros i H;do 10(destruct i as[|i];[first[exact(A 0%nat ltac:(lia))|exact(A 1%nat ltac:(lia))|exact(A 2%nat ltac:(lia))|exact(A 3%nat ltac:(lia))|exact(A 4%nat ltac:(lia))|exact(B 0%nat ltac:(lia))|exact(B 1%nat ltac:(lia))|exact(B 2%nat ltac:(lia))|exact(B 3%nat ltac:(lia))|exact(B 4%nat ltac:(lia))]|]);cbn [right_count] in H;lia)
 ltac:(intros;reflexivity) Start) as [Bounds Value].
 split;[exact Bounds|now rewrite target_value_ok in Value].
Qed.
Lemma call_multiply j (paired:bool) base s : lane_words s -> constants s ->
 split_field(rfield s 0) -> split_field(rfield s 5) ->
 split_field(fun i=>cells s(offset base (64*Z.of_nat i))) ->
 forall start, In start (if paired then [0%nat;5%nat] else [0%nat]) ->
 reduced(rfield(call j (if paired then MultiplyPair else MultiplySingle) base s)start) /\
 represents (limbs(rfield(call j (if paired then MultiplyPair else MultiplySingle) base s)start))
 (limbs(rfield s start)*limbs(fun i=>cells s(offset base(64*Z.of_nat i)))).
Proof.
 intros W C X Y M start Start;destruct paired;
 [pose proof(call_correct j MultiplyPair base s (fun i=>cells s(offset base(64*Z.of_nat i))) start
 W (conj X Y) C I M ltac:(intros;reflexivity) Start) as [B V] |
 pose proof(call_correct j MultiplySingle base s (fun i=>cells s(offset base(64*Z.of_nat i))) start
 W (conj X Y) C I M ltac:(intros;reflexivity) Start) as [B V]];
 split;try(rewrite target_value_ok in V;exact V).
 - destruct Start as[<- | [<- | []]];intros i I;do 5(destruct i as[|i];[apply B;lia|]);lia.
 - destruct Start as[<- | []];intros i I;do 5(destruct i as[|i];[apply B;lia|]);lia.
Qed.
