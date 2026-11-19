From ProofArithmetic Require Import Ranges.
From Coq Require Import List ZArith Bool Lia Ring.
From Machine Require Import Blocks Instructions WordBounds.
Require Import Program CachedAddABI FieldSpec Polynomial Symbolic Kernels KernelInterface Lane Control Bounds.
Import ListNotations. Open Scope Z_scope.
Definition includes a lo hi := (lo<=?lower_bound a)&&(upper_bound a<=?hi).
Lemma includes_sound a lo hi x : includes a lo hi=true ->bounded a x ->lo<=x<=hi.
Proof. unfold includes,bounded;rewrite andb_true_iff,!Z.leb_le;lia. Qed.
Definition kernel_inputs k (b:bstate) bases :=
 forallb(fun i=>includes(fst b i)0(input_bound k i))(seq 0 10) &&
 singleton(fst b 28%nat)19 && singleton(fst b 29%nat)(radix-1) &&
 (negb(needs_bias k) || (singleton(fst b 30%nat)(bias 0) && singleton(fst b 31%nat)(bias 1))) &&
 forallb(fun i=>includes(bload b bases(load_base k)(64*Z.of_nat i))0(right_bound k i))(seq 0(right_count k)).
Lemma bload_sound b s bases base disp : bmodels b s ->
 bounded(bload b bases base disp)(lane_load s bases base disp).
Proof. intros[R M];unfold bload,lane_load;destruct(find _ _)as[[r a]|];auto;unfold bounded;cbn;lia. Qed.
Lemma input_sound k b s bases : bmodels b s ->kernel_inputs k b bases=true ->
 operands k(registers s) /\right_ok k(fun i=>lane_load s bases(load_base k)(64*Z.of_nat i)).
Proof.
 intros Model Check;destruct Model as[R M];unfold kernel_inputs in Check.
 repeat rewrite andb_true_iff in Check;destruct Check as[[[[Reg C]Mask]Bias]Mem].
 rewrite forallb_forall in Reg,Mem.
 split.
 - split.
   + intros i I;eapply includes_sound;[apply Reg, in_seq;lia|apply R].
   + split;[eapply singleton_sound;eauto|];split;[eapply singleton_sound;eauto|].
     intro K;rewrite K in Bias;cbn in Bias;apply andb_true_iff in Bias as[A B];split;eapply singleton_sound;eauto.
 - intros i I;eapply includes_sound;[apply Mem,in_seq;lia|apply bload_sound;split;assumption].
Qed.
Definition target_value k r m start := match k with
 | PrepareAB | PrepareEH=>if Nat.eqb start 0 then pack m 5-pack m 0 else pack m 5+pack m 0
 | PrepareFG=>if Nat.eqb start 0 then pack r 0-pack r 5 else pack r 0+pack r 5
 | Independent=>let src:=if Nat.eqb start 0 then 5%nat else 0%nat in pack r src*pack m src
 | Pair | Single=>pack r start*pack m 0 end.
Local Opaque packE.
Lemma target_value_ok k r m start : val(env r m)(target k start)=target_value k r m start.
Proof.
 destruct k;unfold target,target_value;repeat match goal with |-context[if ?b then _ else _]=>destruct b end;
 cbn [val minus];rewrite ?pack_env_reg,?pack_env_mem;ring.
Qed.
Lemma prefix_words j full affine n s : lane_words s ->lane_words(prefix_state j full affine n s).
Proof.
 intro W;apply lane_effects_words;[|exact W].
 apply Forall_forall;intros e H;assert(H0:In e(expected_path full affine)).
 { rewrite <-(firstn_skipn n(expected_path full affine));apply in_or_app;now left. }
 clear H;rename H0 into H.
 destruct full,affine;vm_compute in H;
 intuition subst;cbn [effect_words];try exact I;unfold word64;lia.
Qed.
Lemma firstn_succ {A}(xs:list A)n e : nth_error xs n=Some e ->firstn(S n)xs=firstn n xs++[e].
Proof. revert xs;induction n;intros[|x xs]H;try discriminate;cbn in *.
 - inversion H;reflexivity.
 - now rewrite(IHn xs H).
Qed.
Lemma prefix_next j full affine n s e : nth_error(expected_path full affine)n=Some e ->
 prefix_state j full affine(S n)s=lane_effect j(prefix_state j full affine n s)e.
Proof.
 intro E;unfold prefix_state,lane_effects,Machine.Lane.lane_effects.
 rewrite (firstn_succ _ _ _ E),fold_left_app;reflexivity.
Qed.
Theorem call_correct j full affine n s k bases start :
 lane_words s ->input_bounds affine s ->
 nth_error(expected_path full affine)n=Some(Evaluate(kernel_id k)bases) ->
 kernel_inputs k(prefix_bounds j full affine n)bases=true ->
 In start(output_starts k) ->
 represents(limbs(rfield(prefix_state j full affine(S n)s)start))
 (target_value k(registers(prefix_state j full affine n s))
 (fun i=>lane_load(prefix_state j full affine n s)bases(load_base k)(64*Z.of_nat i))start).
Proof.
 intros W B Event Check Start;pose proof(prefix_sound j full affine n s W B)as Model.
 destruct(input_sound k _ _ _ Model Check)as[Operands Right].
 rewrite(prefix_next _ _ _ _ _ _ Event).
 destruct(run_correct k (registers(prefix_state j full affine n s))
 (lane_load(prefix_state j full affine n s)bases)
 (fun i=>lane_load(prefix_state j full affine n s)bases(load_base k)(64*Z.of_nat i))start
 (proj1(prefix_words _ _ _ _ _ W))Operands Right ltac:(intros;reflexivity)Start)as[_ V].
 now rewrite target_value_ok in V.
Qed.
