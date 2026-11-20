From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.Blocks execution.WordBounds.
From Ed25519Simd.Scalar Require Import Program ScalarABI ScalarSpec Lane Control Routing.
Import ListNotations. Open Scope Z_scope.
Lemma words_lane m region i j : (j<8)%nat ->
 words_at m region(8*i+j)%nat=m(region,64*Z.of_nat i)j.
Proof.
 intro J;unfold words_at;replace(8*i+j)%nat with(j+i*8)%nat by lia.
 rewrite Nat.div_add,Nat.mod_add,Nat.div_small,Nat.mod_small by lia;now rewrite Nat.add_0_l.
Qed.
Definition output_data d := effects scalar_program expected_path d.
Theorem arithmetic_contract d : data_words d ->
 scalar_spec(words_at(memory d)input)(words_at(memory(output_data d))output).
Proof.
 intros[Regs Mem]j J.
 assert(Words:lane_words(view d j))by(split;[intro;apply Regs,J|intro;apply Mem,J]).
 destruct(lane_correct j(view d j)Words)as[Value Bounds].
 pose proof(view_effects d j(view d j)expected_path ltac:(split;intro;reflexivity))as[R M].
 unfold scalar_spec,lane_input,lane_output;split.
 - transitivity(number B(map(fun i=>cells(lane_effects j expected_path(view d j))(output,64*Z.of_nat i))(seq 0 5))).
   + f_equal;apply map_ext;intro i;rewrite words_lane by exact J;apply M.
   + rewrite Value;f_equal;f_equal;apply map_ext;intro i;symmetry;apply words_lane,J.
 - intros i I;rewrite words_lane by exact J;rewrite M;apply Bounds,I.
Qed.
Theorem scalar_returns_correct initial : valid_scalar_entry initial ->exists final,
 returns scalar_program abi_layout initial final /\stack_restored initial final /\
 scalar_spec(words_at(memory(snd initial))input)(words_at(memory(snd final))output).
Proof.
 destruct initial as[c d];intros[[incoming Init]Words];cbn [fst]in Init;subst c.
 pose proof(control_checked incoming)as Check.
 destruct(path 100 scalar_program abi_layout(initial_control incoming))as[[last es]|]eqn:P;[|discriminate].
 cbn [observe]in Check;injection Check as PC SP R3 R5 R12 R13 R14 R15 Ops;subst es.
 exists(last,output_data d);split;[exact(path_returns _ _ _ _ _ _ P d)|];split.
 - unfold stack_restored, SysV.restores_rsp;cbn [fst];rewrite SP;reflexivity.
 - apply arithmetic_contract,Words.
Qed.
