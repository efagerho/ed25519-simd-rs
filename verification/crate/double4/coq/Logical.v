From Coq Require Import List ZArith Lia.
From Machine Require Import execution.Blocks execution.WordBounds.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Double4 Require Import Program Double4ABI Double4Memory Double4Spec Round KernelInterface Preparation Finish Execution RoundArithmetic.
Import ListNotations. Open Scope Z_scope.
Local Opaque effects double_n doubling.
Lemma read_words m region i j : (j<8)%nat ->
 cell(words_at m region)i j=m(limb_address region i)j.
Proof.
 intro J;unfold cell,words_at.
 assert(D:((i*8+j)/8=i)%nat)by(symmetry;apply Nat.div_unique with(r:=j);lia).
 assert(R:((i*8+j)mod 8=j)%nat)by(symmetry;apply Nat.mod_unique with(q:=i);lia).
 now rewrite D,R.
Qed.
Lemma input_coordinates d j : (j<8)%nat ->
 point_values(words_at(memory d)point)j=lane_coordinates(view d j).
Proof.
 intro J;unfold point_values,point_from_fields,word_coordinate,lane_coordinates,field_at,limbs,field,view;cbn [cx cy cz ct cells].
 repeat rewrite read_words by exact J;reflexivity.
Qed.
Lemma input_lanes d : loose_xyz(words_at(memory d)point) ->
 forall j,(j<8)%nat -> xyz_bounds(view d j).
Proof.
 intros B j J c C;apply(loose_ext (fun i=>cell(words_at(memory d)point)(5*c+i)%nat j));[|apply B;assumption].
 intros i I;rewrite read_words by exact J;reflexivity.
Qed.
Lemma output_spec_from_memory before after j : (j<8)%nat ->
 memory_spec(lane_coordinates(view before j))after j ->
 forall c,(c<4)%nat ->
 reduced(fun i=>cell(words_at(memory after)point)(5*c+i)%nat j) /\
 field_at(words_at(memory after)point)(5*c)%nat j mod prime=
 coordinate(double_n 4(point_values(words_at(memory before)point)j))c mod prime.
Proof.
 intros J S c C;destruct(S c C)as[B V].
 assert(E:forall i,(i<5)%nat ->cell(words_at(memory after)point)(5*c+i)%nat j=
 memory after(point,64*Z.of_nat(5*c+i))j).
 { intros;apply read_words;exact J. }
 split.
 - apply(field_bound_ext _ (fun i=>memory after(point,64*Z.of_nat(5*c+i))j));[intros;symmetry;apply E;assumption|exact B].
 - unfold field_at;rewrite(limbs_ext _ _ E),input_coordinates by exact J;apply represents_mod;exact V.
Qed.
Theorem arithmetic_contract d : data_words d ->
 double4_spec(words_at(memory d)point)(words_at(memory(effects double4_program expected_path d))point).
Proof.
 intros W Bounds j c J C.
 apply(output_spec_from_memory d _ j J);[|exact C].
 apply arithmetic_path_correct;[exact W|exact J|apply input_lanes;assumption].
Qed.
Theorem double4_returns_correct initial pad : valid_double4_entry initial pad ->
 exists final, returns double4_program abi_layout initial final /\ stack_restored initial final /\
 double4_spec(words_at(memory(snd initial))point)(words_at(memory(snd final))point).
Proof.
 destruct initial as[c d];intros[Pad[[incoming[bp[BP Init]]]Words]].
 cbn [fst] in Init;subst c.
 pose proof(control_path_checked incoming pad bp Pad)as Check.
 destruct(path 200 double4_program abi_layout(initial_control incoming pad bp))as[[last es]|]eqn:P;[|discriminate].
 cbn [observe_path] in Check;injection Check as PC SP Ops;subst es.
 exists(last,effects double4_program expected_path d);split.
 - apply(path_returns _ _ _ _ _ _ P).
 - split.
   + unfold stack_restored,SysV.restores_rsp;cbn [fst];rewrite SP.
     change(Some(Ptr(scratch,1296+pad))=Some(Ptr(scratch,(1288+pad)+8))).
     f_equal;f_equal;f_equal;lia.
   + apply arithmetic_contract;exact Words.
Qed.
