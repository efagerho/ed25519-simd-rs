From Coq Require Import List ZArith Bool Lia Ring.
From Machine Require Import Blocks Instructions WordBounds.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Double4 Require Import Program Double4ABI Kernels KernelInterface Round RoundArithmetic Double4Spec Preparation Finish.
Import ListNotations. Open Scope Z_scope.
Local Opaque code stage0 stage1 stage2 stage3 stage4 stage5 stage6.
Lemma round_split j full s : round j full s=finish j full(prepare j s).
Proof.
 unfold round,round_effects,finish,prepare,shuffle,lane_effects,Machine.Lane.lane_effects.
 cbn [stage]. rewrite !fold_left_app. cbn [fold_left].
 rewrite !call_is_effect. reflexivity.
Qed.
Theorem round_correct j full s : lane_words s -> constants s ->
 loose(field s point 0) -> loose(field s point 5) -> loose(field s point 10) ->
 round_result full s (round j full s).
Proof. intros;rewrite round_split;apply finish_correct,prepare_correct;assumption. Qed.
Local Opaque round.
Lemma lane_coordinate s c : (c<4)%nat -> coordinate(lane_coordinates s)c=limbs(field s point(5*c)).
Proof. intros C;do 4(destruct c as[|c];[reflexivity|]);lia. Qed.
Lemma doubling_congruent q r :
 represents(cx q)(cx r) -> represents(cy q)(cy r) -> represents(cz q)(cz r) ->
 forall c,(c<4)%nat -> represents(coordinate(doubling q)c)(coordinate(doubling r)c).
Proof.
 intros X Y Zb c C;do 4(destruct c as[|c];[
 unfold coordinate,doubling;cbn [cx cy cz ct];
 repeat first[assumption|apply ctimes|apply cplus|apply cminus|apply cneg|apply crefl]|]);lia.
Qed.
Local Opaque doubling.
Definition xyz_bounds s := forall c,(c<3)%nat -> loose(field s point(5*c)).
Definition xyz_rep s q := forall c,(c<3)%nat -> represents(limbs(field s point(5*c)))(coordinate q c).
Fixpoint early_rounds j n s := match n with O=>s | S n=>round j false(early_rounds j n s) end.
Theorem early_rounds_correct j n s q : lane_words s -> constants s -> xyz_bounds s -> xyz_rep s q ->
 let out:=early_rounds j n s in
 lane_words out /\ constants out /\ xyz_bounds out /\ xyz_rep out(double_n n q).
Proof.
 intros W C Bounds Rep;induction n as[|n [Wn[Cn[Bn Rn]]]];[exact(conj W(conj C(conj Bounds Rep)))|].
 pose proof(round_correct j false (early_rounds j n s) Wn Cn
 (Bn 0%nat ltac:(lia))(Bn 1%nat ltac:(lia))(Bn 2%nat ltac:(lia)))as[Wo[Co Ro]].
 split;[exact Wo|]. split;[exact Co|]. split.
 - intros c H;apply reduced_loose;apply(Ro c H).
 - intros c H. destruct(Ro c H)as[B V].
   eapply ctrans;[exact V|]. apply doubling_congruent;try lia.
   + exact(Rn 0%nat ltac:(lia)).
   + exact(Rn 1%nat ltac:(lia)).
   + exact(Rn 2%nat ltac:(lia)).
Qed.
Local Opaque early_rounds.
Definition four_rounds j s := round j true(early_rounds j 3 s).
Theorem four_rounds_correct j s : lane_words s -> constants s -> xyz_bounds s ->
 let out:=four_rounds j s in lane_words out /\ constants out /\
 forall c,(c<4)%nat -> reduced(field out point(5*c)) /\
 represents(limbs(field out point(5*c)))(coordinate(double_n 4(lane_coordinates s))c).
Proof.
 intros W C B.
 assert(Rep:xyz_rep s (lane_coordinates s)).
 { intros c H;rewrite lane_coordinate by lia;apply crefl. }
 destruct(early_rounds_correct j 3 s (lane_coordinates s) W C B Rep)as[W3[C3[B3 R3]]].
 destruct(round_correct j true (early_rounds j 3 s) W3 C3
 (B3 0%nat ltac:(lia))(B3 1%nat ltac:(lia))(B3 2%nat ltac:(lia)))as[Wo[Co Ro]].
 split;[exact Wo|]. split;[exact Co|]. intros c H;destruct(Ro c H)as[Bound V].
 split;[exact Bound|]. eapply ctrans;[exact V|]. apply doubling_congruent;try lia.
 - exact(R3 0%nat ltac:(lia)).
 - exact(R3 1%nat ltac:(lia)).
 - exact(R3 2%nat ltac:(lia)).
Qed.
Definition initialize j s := lane_effects j [Broadcast 28 19;Broadcast 29(radix-1)] s.
Lemma initialize_words j s : lane_words s -> lane_words(initialize j s).
Proof. apply lane_effects_words;repeat constructor;unfold effect_words,word64,radix;lia. Qed.
Lemma initialize_constants j s : constants(initialize j s).
Proof. split;reflexivity. Qed.
Lemma initialize_field j s region coord i : field(initialize j s)region coord i=field s region coord i.
Proof. reflexivity. Qed.
Lemma initialize_coordinates j s : lane_coordinates(initialize j s)=lane_coordinates s.
Proof. reflexivity. Qed.
Local Transparent round early_rounds.
Lemma path_lanes j s : lane_effects j expected_path s=
 lane_effect j (four_rounds j (initialize j s)) ClearUpper.
Proof. unfold expected_path,initialize,four_rounds;cbn [early_rounds].
 unfold lane_effects,Machine.Lane.lane_effects,round;rewrite !fold_left_app;reflexivity. Qed.
Local Opaque round early_rounds.
Local Opaque effects.
Definition lane_spec q s := forall c,(c<4)%nat ->
 reduced(field s point(5*c)) /\
 represents(limbs(field s point(5*c)))(coordinate(double_n 4 q)c).
Definition memory_spec q d j := forall c,(c<4)%nat ->
 let f:=fun i=>memory d(point,64*Z.of_nat(5*c+i))j in
 reduced f /\ represents(limbs f)(coordinate(double_n 4 q)c).
Lemma clear_spec j q s : lane_spec q s -> lane_spec q(lane_effect j s ClearUpper).
Proof. exact(fun H=>H). Qed.
Lemma lane_to_memory d j s q : lane_models d j s -> lane_spec q s -> memory_spec q d j.
Proof.
 intros[_ M] Spec c C;destruct(Spec c C)as[B V].
 assert(E:forall i,(i<5)%nat -> memory d(point,64*Z.of_nat(5*c+i))j=field s point(5*c)i).
 { intros;apply M. }
 split.
 - apply(field_bound_ext _ (field s point(5*c)));[intros;symmetry;apply E;assumption|exact B].
 - rewrite(limbs_ext _ _ E);exact V.
Qed.
Lemma lane_path_correct j s : lane_words s -> xyz_bounds s ->
 lane_spec(lane_coordinates s)(lane_effects j expected_path s).
Proof.
 intros W B;rewrite path_lanes;apply clear_spec.
 pose proof(four_rounds_correct j (initialize j s) (initialize_words j s W)
 (initialize_constants j s) B) as[_[_ Result]].
 rewrite initialize_coordinates in Result;exact Result.
Qed.
Theorem arithmetic_path_correct d j : data_words d -> (j<8)%nat ->
 xyz_bounds(view d j) -> memory_spec(lane_coordinates(view d j))(effects double4_program expected_path d)j.
Proof.
 intros[W M] J B.
 apply(lane_to_memory _ _ (lane_effects j expected_path(view d j))).
 - apply view_effects;split;reflexivity.
 - apply lane_path_correct;[split;intro;[apply W|apply M];exact J|exact B].
Qed.
