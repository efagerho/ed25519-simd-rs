From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.Blocks isa.Instructions execution.WordBounds.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.CachedAdd Require Import Program CachedAddABI CachedAddMemory CachedAddSpec Lane Control Bounds KernelCalls Routing Arithmetic.
Import ListNotations. Open Scope Z_scope.
Lemma path_length full affine : length(expected_path full affine)=67%nat.
Proof. destruct full,affine;reflexivity. Qed.
Lemma complete_prefix j full affine s : prefix_state j full affine 67 s=lane_effects j(expected_path full affine)s.
Proof. unfold prefix_state;rewrite firstn_all2;[reflexivity|rewrite path_length;lia]. Qed.
Lemma bounds_checked j full affine :
 let output := snd (prefix_bounds j full affine 67) in
 forallb (fun i => includes (output (point,64*Z.of_nat i)) 0
   (Radix51.output_bound (i mod 5))) (seq 0 20) = true.
Proof. destruct full,affine;vm_compute;reflexivity. Qed.
Lemma final_bounds j full affine s c i : lane_words s ->Bounds.input_bounds affine s ->
 (c<4)%nat ->(i<5)%nat ->0<=M j full affine 67 s point(5*c)i<=Radix51.output_bound i.
Proof.
 intros W B C I;pose proof(bounds_checked j full affine)as Check;rewrite forallb_forall in Check.
 specialize(Check(5*c+i)%nat ltac:(apply in_seq;lia)).
 assert(Mod:((5*c+i)mod 5=i)%nat)by(symmetry;apply Nat.mod_unique with(q:=c);lia).
 rewrite Mod in Check.
 apply(includes_sound _ _ _ _ Check);apply(prefix_sound j full affine 67 s W B).
Qed.
Lemma input_lane affine d j : (j<8)%nat ->
 CachedAddSpec.input_bounds affine(words_at(memory d)point)(words_at(memory d)cached) ->
 Bounds.input_bounds affine(view d j).
Proof.
 intros J[P C][r off]H;unfold input_cell in H;cbn [fst snd]in H.
 repeat rewrite andb_true_iff in H;destruct H as[[Region L]Align].
 apply Z.leb_le in L;apply Z.eqb_eq in Align.
 assert(D:off=64*Z.of_nat(Z.to_nat(off/64))).
 { rewrite Z2Nat.id by(apply Z.div_pos;lia);pose proof(Z.div_mod off 64 ltac:(lia));lia. }
 apply orb_true_iff in Region;destruct Region as[Point|Cache];
 apply andb_true_iff in Point || apply andb_true_iff in Cache.
 - destruct Point as[R U];apply Nat.eqb_eq in R;subst r;apply Z.ltb_lt in U.
   specialize(P(Z.to_nat(off/64))j ltac:(assert(off/64<20)by(apply Z.div_lt_upper_bound;lia);cbn;lia)J).
   rewrite cell_words_at in P by exact J.
   change (0<=memory d (point,off) j<cached_point_limit (Z.to_nat(off/64))).
   unfold vector_address in P; cbn [Z.add] in P. now rewrite <-D in P.
 - destruct Cache as[R U];apply Nat.eqb_eq in R;subst r;apply Z.ltb_lt in U.
   specialize(C(Z.to_nat(off/64))j ltac:(destruct affine;cbn [cache_length]in U;
    [assert(off/64<15)by(apply Z.div_lt_upper_bound;lia)|assert(off/64<20)by(apply Z.div_lt_upper_bound;lia)];lia)J).
   rewrite cell_words_at in C by exact J;rewrite D;exact C.
Qed.
Lemma input_values d j r c : (j<8)%nat ->
 word_coordinate(words_at(memory d)r)j c=lane_value(view d j)r c.
Proof. intro J;unfold word_coordinate,field_at,limbs,lane_value,field,view;cbn [cells].
 repeat rewrite cell_words_at by exact J;reflexivity. Qed.
Definition output_data full affine d := effects add_cached_program(expected_path full affine)d.
Lemma output_view full affine d j : lane_models(output_data full affine d)j
 (prefix_state j full affine 67(view d j)).
Proof. rewrite complete_prefix;apply view_effects;split;reflexivity. Qed.
Lemma output_limb full affine d j c i : (j<8)%nat ->
 cell(words_at(memory(output_data full affine d))point)(5*c+i)%nat j=
 M j full affine 67(view d j)point(5*c)i.
Proof. intro J;rewrite cell_words_at by exact J;apply(output_view full affine d j). Qed.
Lemma output_value full affine d j c : (j<8)%nat ->
 word_coordinate(words_at(memory(output_data full affine d))point)j c=
 limbs(M j full affine 67(view d j)point(5*c)).
Proof. intro J;unfold word_coordinate,field_at;apply limbs_ext;intros;apply output_limb;exact J. Qed.
Theorem arithmetic_contract full affine d : data_words d ->
 cached_add_spec full affine(words_at(memory d)point)(words_at(memory d)cached)
 (words_at(memory(output_data full affine d))point).
Proof.
 intros[R W];split.
 - intros Full i j I J;subst full;change(cell(words_at(memory(output_data false affine d))point)(5*3+i)%nat j=0).
   rewrite output_limb by exact J;apply out_zero;exact I.
 - intros B j c J C.
   assert(Words:lane_words(view d j))by(split;intro;[apply R|apply W];exact J).
   pose proof(input_lane affine d j J B)as Input;split.
   + intros i I;rewrite output_limb by exact J;apply final_bounds;assumption.
   + rewrite output_value by exact J.
     unfold point_values,cache_values,point_from_fields,cache_from_fields.
     repeat rewrite input_values by exact J.
     apply represents_mod,arithmetic_coordinates;assumption.
Qed.
Theorem cached_add_returns_correct initial pad full affine : valid_cached_add_entry initial pad full affine ->
 exists final,returns add_cached_program(abi_layout affine)initial final /\stack_restored initial final /\
 cached_add_spec full affine(words_at(memory(snd initial))point)(words_at(memory(snd initial))cached)
 (words_at(memory(snd final))point).
Proof.
 destruct initial as[c d];intros[Pad[[incoming[bp[BP Init]]]Words]].
 cbn [fst]in Init;subst c;pose proof(control_path_checked incoming pad bp full affine Pad)as Check.
 destruct(path 200 add_cached_program(abi_layout affine)(initial_control incoming pad bp full affine))as[[last es]|]eqn:P;[|discriminate].
 cbn [observe_path]in Check;injection Check as PC SP Ops;subst es.
 exists(last,output_data full affine d);split.
 - apply(path_returns _ _ _ _ _ _ P).
 - split.
   + unfold stack_restored,SysV.restores_rsp;cbn [fst];rewrite SP.
     change(Some(Ptr(scratch,1296+pad))=Some(Ptr(scratch,(1288+pad)+8))).
     f_equal;f_equal;f_equal;lia.
   + apply arithmetic_contract;exact Words.
Qed.
