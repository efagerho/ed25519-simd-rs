From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks Instructions WordBounds Dependencies.
Require Import Program CachedAddABI FieldSpec.
Import ListNotations. Open Scope Z_scope.
From Machine Require Export Lane.
Definition lane_effect := Machine.Lane.lane_effect add_cached_program.
Definition lane_effects := Machine.Lane.lane_effects add_cached_program.
Lemma view_effect d j s e : lane_models d j s ->
 lane_models (apply_effect add_cached_program d e) j (lane_effect j s e).
Proof. apply (Machine.Lane.view_effect add_cached_program). Qed.
Lemma view_effects d j s es : lane_models d j s ->
 lane_models (effects add_cached_program es d) j (lane_effects j es s).
Proof. apply (Machine.Lane.view_effects add_cached_program). Qed.
Lemma lane_effect_words j s e : effect_words e -> lane_words s -> lane_words (lane_effect j s e).
Proof. apply (Machine.Lane.lane_effect_words add_cached_program). Qed.
Lemma lane_effects_words j es s : Forall effect_words es -> lane_words s -> lane_words (lane_effects j es s).
Proof. apply (Machine.Lane.lane_effects_words add_cached_program). Qed.
Definition field s region coord := fun i=>cells s(region,64*Z.of_nat(coord+i)).
Definition rfield s reg := fun i=>registers s(reg+i)%nat.
