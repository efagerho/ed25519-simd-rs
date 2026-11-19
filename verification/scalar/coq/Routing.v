From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks Instructions WordBounds Dependencies.
Require Import Program ScalarABI ScalarSpec ScalarMath Product Unpack Reduction Montgomery Finish Calculate Lane Control.
Import ListNotations. Open Scope Z_scope.
Definition no_memory(_:nat)(_:Z) := 0.
Definition loaded s := run(lane_load s[(6%nat,(input,0))])(fragment_code scalar_program 0)(registers s).
Definition setup r := put(put(put(put(put(put r 28%nat l0)29%nat l1)30%nat l2)27%nat l4)31%nat factor)26%nat(B-1).
Definition before_tail j s := lane_effects j(firstn 24 expected_path)s.
Definition tail_code := fragment_code scalar_program 7++fragment_code scalar_program 8++
 fragment_code scalar_program 9++fragment_code scalar_program 10++fragment_code scalar_program 11.
Lemma run_app load a b r : run load(a++b)r=run load b(run load a r).
Proof. revert r;induction a as[|[d op]a IH];intro r;cbn [run app];auto. Qed.
Local Opaque run fragment_code.
Lemma prefix_registers j s i : registers(before_tail j s)i=
 setup(multiply 5 no_memory(run no_memory Unpack.code(put(loaded s)29%nat(B-1))))i.
Proof.
 unfold before_tail,expected_path,lane_effects.
 cbn [firstn fold_left lane_effect registers cells lane_load find fst snd Nat.eqb].
 unfold setup,loaded,Unpack.code.
 cbn [multiply with_constants product_code Nat.add].
 cbv [lane_load find fst snd Nat.eqb].
 reflexivity.
Qed.
Local Transparent fragment_code run.
Lemma tail_decomposition : tail_code=
 [(23%nat,Xor 23 23)]++Reduction.code 0++Reduction.code 1++Reduction.code 2++Reduction.code 3++Reduction.code 4++
 normalize_code++Finish.code.
Proof. vm_compute;reflexivity. Qed.
Local Opaque fragment_code run Reduction.code normalize_code Finish.code.
Lemma reduce_ext n load r s : (forall i,r i=s i)->forall i,reduce n load r i=reduce n load s i.
Proof. intro E;induction n;cbn [reduce];[exact E|apply run_ext;[reflexivity|exact IHn]]. Qed.
Lemma tail_calculate j s i : run no_memory tail_code(registers(before_tail j s))i=calculate no_memory(loaded s)i.
Proof.
 rewrite tail_decomposition,!run_app.
 change(run no_memory Finish.code(run no_memory normalize_code
 (reduce 5 no_memory(put(registers(before_tail j s))23%nat
 (Logic.vpxorq(registers(before_tail j s)23%nat)(registers(before_tail j s)23%nat)))))i=calculate no_memory(loaded s)i).
 unfold Logic.vpxorq;rewrite Z.lxor_nilpotent.
 unfold calculate.
 apply run_ext;[reflexivity|];apply run_ext;[reflexivity|].
 assert(Start:forall k,put(registers(before_tail j s))23%nat 0 k=
 prepare(multiply 5 no_memory(run no_memory Unpack.code(put(loaded s)29%nat(B-1))))k).
 { intro k;unfold put,prepare;rewrite Nat.eqb_sym;destruct(Nat.eqb k 23);[reflexivity|].
   rewrite prefix_registers;unfold setup,put,constants.
   do 32(destruct k as[|k];[reflexivity|]);reflexivity. }
 apply reduce_ext,Start.
Qed.
Lemma full_split : expected_path=firstn 24 expected_path++skipn 24 expected_path.
Proof. symmetry;apply firstn_skipn. Qed.
Lemma effects_split j s : lane_effects j expected_path s=
 lane_effects j(skipn 24 expected_path)(before_tail j s).
Proof. unfold before_tail. unfold lane_effects. rewrite <-fold_left_app. rewrite firstn_skipn. reflexivity. Qed.
Local Transparent fragment_code.
Lemma later_saved k i load r : (8<=k<12)%nat ->(i+8<=k)%nat ->
 run load(fragment_code scalar_program k)r i=r i.
Proof.
 intros K I;apply untouched.
 assert(Ks:k=8%nat \/k=9%nat \/k=10%nat \/k=11%nat)by lia.
 destruct Ks as[-> | [-> | [-> | ->]]];
 do 4(destruct i as[|i];[first[lia|vm_compute;reflexivity]|]);lia.
Qed.
Local Opaque fragment_code.
Lemma tail_routing j s i : (i<5)%nat ->
 cells(lane_effects j(skipn 24 expected_path)s)(output,64*Z.of_nat i)=
 run no_memory tail_code(registers s)i.
Proof.
 intro I;unfold lane_effects at 1.
 let es:=eval vm_compute in(skipn 24 expected_path)in change(skipn 24 expected_path)with es.
 cbn [fold_left lane_effect cells registers].
 cbv [lane_load find].
 unfold tail_code;rewrite !run_app.
 assert(Cases:i=0%nat \/i=1%nat \/i=2%nat \/i=3%nat \/i=4%nat)by lia.
 destruct Cases as[-> | [-> | [-> | [-> | ->]]]];
 repeat match goal with |- context[ptr_eq ?a ?b]=>
   let v:=eval vm_compute in(ptr_eq a b)in change(ptr_eq a b)with v end;
 cbv beta iota zeta;
 try rewrite(later_saved 11 _ no_memory _)by lia;
 try rewrite(later_saved 10 _ no_memory _)by lia;
 try rewrite(later_saved 9 _ no_memory _)by lia;
 try rewrite(later_saved 8 _ no_memory _)by lia;reflexivity.
Qed.
Lemma output_routing j s i : (i<5)%nat ->
 cells(lane_effects j expected_path s)(output,64*Z.of_nat i)=
 run no_memory tail_code(registers(before_tail j s))i.
Proof. intro I;rewrite effects_split;apply tail_routing,I. Qed.
Lemma loaded_words s : lane_words s ->forall i,word64(loaded s i).
Proof.
 intros[R M];unfold loaded;apply run_words;[|exact R].
 intros b d;unfold lane_load;destruct(find _ _)as[[base a]|];[apply M|unfold word64;lia].
Qed.
Lemma loaded_input s i : (i<8)%nat ->loaded s i=cells s(input,64*Z.of_nat i).
Proof.
 intro I;unfold loaded.
 let c:=eval vm_compute in(fragment_code scalar_program 0)in change(fragment_code scalar_program 0)with c.
 do 8(destruct i as[|i];[reflexivity|]);lia.
Qed.
Local Opaque calculate lane_effects loaded before_tail tail_code.
Theorem lane_correct j s : lane_words s ->
 number B(map(fun i=>cells(lane_effects j expected_path s)(output,64*Z.of_nat i))(seq 0 5))=
 number W(map(fun i=>cells s(input,64*Z.of_nat i))(seq 0 8))mod L /\
 (forall i,(i<5)%nat->0<=cells(lane_effects j expected_path s)(output,64*Z.of_nat i)<B).
Proof.
 intro Words;destruct(calculate_correct no_memory(loaded s)ltac:(intros;unfold no_memory,word64;lia)(loaded_words s Words))as[Value Bounds].
 split.
 - transitivity(pack(calculate no_memory(loaded s))0).
   + unfold pack.
     apply(f_equal(number B)). apply map_ext_in. intros i I. apply in_seq in I.
     rewrite output_routing by lia. rewrite tail_calculate. reflexivity.
   + rewrite Value. apply(f_equal(fun z=>z mod L)). apply(f_equal(number W)).
     apply map_ext_in;intros i I;apply in_seq in I;apply loaded_input;lia.
 - intros i I;rewrite output_routing,tail_calculate by exact I;apply Bounds,I.
Qed.
