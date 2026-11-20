From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks Instructions WordBounds Dependencies.
Require Import Program Double4ABI FieldSpec Polynomial Kernels KernelInterface.
Import ListNotations. Open Scope Z_scope.
Definition kernel_id k := match k with AddReduce=>2%nat | SquarePair=>7%nat |
 SubtractReduce=>4%nat | MultiplyPair=>8%nat | MultiplySingle=>9%nat end.
Lemma kernel_link k : fragment_code double4_program (kernel_id k)=code k.
Proof. destruct k;vm_compute;reflexivity. Qed.
Definition save region coord reg := map (fun i=>Write (reg+i)%nat (region,64*Z.of_nat(coord+i))) (seq 0 5).
Definition kernel_effect k base := Evaluate (kernel_id k)
 (match k with AddReduce | SquarePair=>[] | _=>[(load_base k,base)] end).
Definition stage0 := [Evaluate 1 [(7%nat,(point,0))]].
Definition stage1 := save scratch 15 10.
Definition stage2 := save scratch 0 0 ++ save scratch 5 5 ++
 [Evaluate 3 [(7%nat,(point,0));(6%nat,(scratch,0))]].
Definition stage3 := [Broadcast 30 (bias 0);Broadcast 31 (bias 1)].
Definition stage4 := save scratch 0 0 ++ save scratch 5 10 ++ save scratch 10 15 ++
 save scratch 15 5 ++ [Evaluate 5 []].
Definition stage5 (full:bool) := save point 0 0 ++ save point 10 5 ++
 [Evaluate 6 [(6%nat,(scratch,0))]] ++ if full then [Evaluate 0 [(6%nat,(scratch,0))]] else [].
Definition stage6 (full:bool) := save point 5 0 ++ if full then save point 15 5 else [].
Definition round_effects (full:bool) := stage0 ++ [kernel_effect AddReduce (scratch,0)] ++ stage1 ++
 [kernel_effect SquarePair (scratch,0)] ++ stage2 ++ [kernel_effect SquarePair (scratch,0)] ++ stage3 ++
 [kernel_effect SubtractReduce (scratch,0)] ++ stage4 ++ [kernel_effect MultiplyPair (scratch,640)] ++
 stage5 full ++ [kernel_effect (if full then MultiplyPair else MultiplySingle) (scratch,960)] ++ stage6 full.
Definition expected_path := [Broadcast 28 19;Broadcast 29 (radix-1)] ++
 round_effects false ++ round_effects false ++ round_effects false ++ round_effects true ++ [ClearUpper].
Definition observe_path (result:option(control * list effect)) := match result with
 | Some(c,es)=>Some(rip c,Blocks.gpr c 4%nat,es) | _=>None end.
Theorem block_layout_checked : valid_program double4_program=true.
Proof. vm_compute;reflexivity. Qed.
Theorem control_path_checked incoming pad bp : permitted_padding pad ->
 observe_path (path 200 double4_program abi_layout (initial_control incoming pad bp)) =
 Some (Caller,Ptr(scratch,1296+pad),expected_path).
Proof.
 intros [<- | [<- | [<- | [<- | []]]]]; vm_compute;reflexivity.
Qed.

From Machine Require Export Lane.
Definition lane_effect := Machine.Lane.lane_effect double4_program.
Definition lane_effects := Machine.Lane.lane_effects double4_program.
Lemma view_effect d j s e : lane_models d j s ->
 lane_models (apply_effect double4_program d e) j (lane_effect j s e).
Proof. apply (Machine.Lane.view_effect double4_program). Qed.
Lemma view_effects d j s es : lane_models d j s ->
 lane_models (effects double4_program es d) j (lane_effects j es s).
Proof. apply (Machine.Lane.view_effects double4_program). Qed.
Lemma lane_effect_words j s e : effect_words e -> lane_words s -> lane_words (lane_effect j s e).
Proof. apply (Machine.Lane.lane_effect_words double4_program). Qed.
Lemma lane_effects_words j es s : Forall effect_words es -> lane_words s -> lane_words (lane_effects j es s).
Proof. apply (Machine.Lane.lane_effects_words double4_program). Qed.
Definition constants s := registers s 28%nat=19 /\ registers s 29%nat=radix-1.
Definition field s region coord := fun i=>cells s (region,64*Z.of_nat(coord+i)).
Definition rfield s reg := get (registers s) reg.
Definition shuffle j es s := lane_effects j es s.
Definition call (j:nat) k base s := Lane
 (run (lane_load s (match k with AddReduce | SquarePair=>[] | _=>[(load_base k,base)] end)) (code k) (registers s)) (cells s).
Lemma call_is_effect j k base s : lane_effect j s (kernel_effect k base)=call j k base s.
Proof. unfold call,kernel_effect;cbn [lane_effect Machine.Lane.lane_effect];rewrite kernel_link;reflexivity. Qed.
Definition round j full s := lane_effects j (round_effects full) s.
Local Opaque code.
Lemma call_registers j k base s : registers (call j k base s)=
 run (lane_load s (match k with AddReduce | SquarePair=>[] | _=>[(load_base k,base)] end)) (code k) (registers s).
Proof. reflexivity. Qed.
Lemma call_cells j k base s : cells (call j k base s)=cells s.
Proof. destruct k;reflexivity. Qed.
Lemma kernel_constants j k base s : constants s -> constants (call j k base s).
Proof.
 intros [C M];unfold constants;rewrite call_registers;split;rewrite untouched;auto;
 destruct k;vm_compute;reflexivity.
Qed.
Ltac five := intros i I;do 5 (destruct i as [|i];[reflexivity|]);lia.
Lemma stage0_x j s : forall i,(i<5)%nat -> rfield (shuffle j stage0 s) 0 i=field s point 0 i.
Proof. five. Qed.
Lemma stage0_y j s : forall i,(i<5)%nat -> rfield (shuffle j stage0 s) 5 i=field s point 5 i.
Proof. five. Qed.
Lemma stage1_xy j s : forall i,(i<10)%nat -> registers (shuffle j stage1 s) i=registers s i.
Proof. intros;reflexivity. Qed.
Lemma stage1_sum j s : forall i,(i<5)%nat -> field (shuffle j stage1 s) scratch 15 i=rfield s 10 i.
Proof. five. Qed.
Lemma stage2_z j s : forall i,(i<5)%nat -> rfield (shuffle j stage2 s) 0 i=field s point 10 i.
Proof. five. Qed.
Lemma stage2_sum j s : forall i,(i<5)%nat -> rfield (shuffle j stage2 s) 5 i=field s scratch 15 i.
Proof. five. Qed.
Lemma stage2_a j s : forall i,(i<5)%nat -> field (shuffle j stage2 s) scratch 0 i=rfield s 0 i.
Proof. five. Qed.
Lemma stage2_b j s : forall i,(i<5)%nat -> field (shuffle j stage2 s) scratch 5 i=rfield s 5 i.
Proof. five. Qed.
Lemma stage3_regs j s : forall i,(i<10)%nat -> registers (shuffle j stage3 s) i=registers s i.
Proof. intros i I;do 10(destruct i as[|i];[reflexivity|]);lia. Qed.
Lemma stage3_bias j s : registers (shuffle j stage3 s) 30%nat=bias 0 /\ registers (shuffle j stage3 s) 31%nat=bias 1.
Proof. split;reflexivity. Qed.
Lemma stage4_e j s : forall i,(i<5)%nat -> field (shuffle j stage4 s) scratch 0 i=rfield s 0 i.
Proof. five. Qed.
Lemma stage4_g j s : forall i,(i<5)%nat -> field (shuffle j stage4 s) scratch 5 i=rfield s 10 i.
Proof. five. Qed.
Lemma stage4_f j s : forall i,(i<5)%nat -> field (shuffle j stage4 s) scratch 10 i=rfield s 15 i.
Proof. five. Qed.
Lemma stage4_h j s : forall i,(i<5)%nat -> field (shuffle j stage4 s) scratch 15 i=rfield s 5 i.
Proof. five. Qed.
Lemma stage4_x j s : forall i,(i<5)%nat -> rfield (shuffle j stage4 s) 0 i=rfield s 0 i.
Proof. five. Qed.
Lemma stage4_z j s : forall i,(i<5)%nat -> rfield (shuffle j stage4 s) 5 i=rfield s 10 i.
Proof. five. Qed.
Lemma stage5_g j full s : forall i,(i<5)%nat -> rfield (shuffle j (stage5 full) s) 0 i=field s scratch 5 i.
Proof. destruct full;five. Qed.
Lemma stage5_e j s : forall i,(i<5)%nat -> rfield (shuffle j (stage5 true) s) 5 i=field s scratch 0 i.
Proof. five. Qed.
Lemma stage5_x j full s : forall i,(i<5)%nat -> field (shuffle j (stage5 full) s) point 0 i=rfield s 0 i.
Proof. destruct full;five. Qed.
Lemma stage5_z j full s : forall i,(i<5)%nat -> field (shuffle j (stage5 full) s) point 10 i=rfield s 5 i.
Proof. destruct full;five. Qed.
Lemma stage6_y j full s : forall i,(i<5)%nat -> field (shuffle j (stage6 full) s) point 5 i=rfield s 0 i.
Proof. destruct full;five. Qed.
Lemma stage6_t j s : forall i,(i<5)%nat -> field (shuffle j (stage6 true) s) point 15 i=rfield s 5 i.
Proof. five. Qed.
Definition stage n full := match n with
 | 0%nat=>stage0 | 1%nat=>stage1 | 2%nat=>stage2 | 3%nat=>stage3
 | 4%nat=>stage4 | 5%nat=>stage5 full | 6%nat=>stage6 full | _=>[] end.
Lemma stage_words n full : Forall effect_words (stage n full).
Proof.
 apply Forall_forall;intros e H.
 do 7(destruct n as[|n];[destruct full;
   cbn [stage stage0 stage1 stage2 stage3 stage4 stage5 stage6 save seq map app In] in H;
   intuition subst;cbn [effect_words bias Nat.eqb];unfold word64;lia|]);contradiction.
Qed.
Lemma stage_constants j n full s : constants s -> constants (shuffle j (stage n full) s).
Proof. do 7(destruct n as[|n];[destruct full;intro C;change (constants s);exact C|]);auto. Qed.
Lemma shuffle_words j n full s : lane_words s -> lane_words (shuffle j (stage n full) s).
Proof. apply lane_effects_words,stage_words. Qed.
Lemma stage0_cells j s a : cells(shuffle j stage0 s)a=cells s a.
Proof. reflexivity. Qed.
Lemma stage3_cells j s a : cells(shuffle j stage3 s)a=cells s a.
Proof. reflexivity. Qed.
Lemma point_unchanged j n full s coord i : (n<5)%nat ->
 field(shuffle j (stage n full)s)point coord i=field s point coord i.
Proof. intro N;do 5(destruct n as[|n];[reflexivity|]);lia. Qed.
Lemma stage5_scratch j full s coord i : field(shuffle j(stage5 full)s)scratch coord i=field s scratch coord i.
Proof. destruct full;reflexivity. Qed.
Lemma stage5_other j s : forall i,(i<5)%nat -> rfield(shuffle j(stage5 false)s)5 i=rfield s 5 i.
Proof. five. Qed.
Lemma stage6_x j full s : forall i,(i<5)%nat -> field(shuffle j(stage6 full)s)point 0 i=field s point 0 i.
Proof. destruct full;five. Qed.
Lemma stage6_z j full s : forall i,(i<5)%nat -> field(shuffle j(stage6 full)s)point 10 i=field s point 10 i.
Proof. destruct full;five. Qed.
Lemma add_inputs j s i : (i<10)%nat -> registers(call j AddReduce (scratch,0)s)i=registers s i.
Proof. intro I;rewrite call_registers;apply untouched.
 do 10(destruct i as[|i];[vm_compute;reflexivity|]);lia. Qed.
Lemma call_field j k base s region coord i : field(call j k base s)region coord i=field s region coord i.
Proof. unfold field;rewrite call_cells;reflexivity. Qed.
Lemma stage1_registers j s r : registers(shuffle j stage1 s)r=registers s r.
Proof. reflexivity. Qed.
Lemma stage6_words j full s : lane_words s -> lane_words(shuffle j(stage6 full)s).
Proof. apply(shuffle_words j 6 full). Qed.
