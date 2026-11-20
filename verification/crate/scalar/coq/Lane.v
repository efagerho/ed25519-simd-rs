From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks Instructions WordBounds Dependencies.
From Ed25519Simd.Scalar Require Import Program ScalarABI.
Import ListNotations. Open Scope Z_scope.
From Machine Require Export Lane.
Definition lane_effect := Machine.Lane.lane_effect scalar_program.
Definition lane_effects := Machine.Lane.lane_effects scalar_program.
Lemma view_effect d j s e : lane_models d j s ->
 lane_models (apply_effect scalar_program d e) j (lane_effect j s e).
Proof. apply (Machine.Lane.view_effect scalar_program). Qed.
Lemma view_effects d j s es : lane_models d j s ->
 lane_models (effects scalar_program es d) j (lane_effects j es s).
Proof. apply (Machine.Lane.view_effects scalar_program). Qed.
Lemma lane_effect_words j s e : effect_words e -> lane_words s -> lane_words (lane_effect j s e).
Proof. apply (Machine.Lane.lane_effect_words scalar_program). Qed.
Lemma lane_effects_words j es s : Forall effect_words es -> lane_words s -> lane_words (lane_effects j es s).
Proof. apply (Machine.Lane.lane_effects_words scalar_program). Qed.
