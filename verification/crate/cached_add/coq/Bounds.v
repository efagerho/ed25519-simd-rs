From ProofArithmetic Require Import Ranges.
From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.Blocks isa.Instructions execution.WordBounds.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Curve25519 Require Import FieldPolynomial.
From Ed25519Simd Require Import FieldSymbolic.
From Ed25519Simd.CachedAdd Require Import Program CachedAddABI Lane Control Kernels.
Import ListNotations. Open Scope Z_scope.
Definition bexec (loads:nat->Z->bounds) s dst op := match op with
 | Load b d=>loads b d
 | MaddMem high a b d=>range_eval(madd_inputs(s dst)(s a)(loads b d))
     (madd_expr high (V 0)(V 1)(V 2))
 | _=>match rhs dst op with Some e=>range_eval s e | None=>s dst end end.
Fixpoint brun loads code s := match code with []=>s | (d,op)::tail=>
 brun loads tail(put s d(bexec loads s d op)) end.
Lemma brun_bounds loads load code s r :
 (forall b d,In(b,d)(loads_of code)->bounded(loads b d)(load b d)) ->
 (forall i,bounded(s i)(r i)) ->r 29%nat=radix-1 ->
 forallb legal_instruction code=true ->
 forall i,bounded(brun loads code s i)(run load code r i).
Proof.
 revert s r;induction code as[|[d op]tail IH];intros s r M R Mask Legal;[exact R|].
 apply andb_true_iff in Legal as[Head Tail];unfold legal_instruction in Head.
 repeat rewrite andb_true_iff in Head;destruct Head as[[[Enc Dest]Form]Leg].
 apply negb_true_iff in Dest;cbn [brun run];apply IH;auto.
 - intros b off H;apply M;unfold loads_of in *;cbn [flat_map snd];apply in_or_app;now right.
 - intro i;unfold put;destruct(Nat.eqb d i);[|apply R].
   change(bounded(bexec loads s d op)(bits load r d op)).
   destruct op;cbn [bexec rhs Machine.symbolic.Expressions.rhs legal_rhs] in *;
     try(erewrite rhs_ok by (eassumption || reflexivity);apply range_eval_sound;assumption).
   + apply M;now left.
   + change (bounded
       (range_eval (madd_inputs (s d) (s a) (loads base disp)) (madd_expr high (V 0) (V 1) (V 2)))
       (IFMA.madd52 high (r d) (r a) (load base disp))).
     rewrite madd_value;apply range_eval_sound;[|destruct high;reflexivity].
     intro k;unfold madd_inputs;destruct(Nat.eqb k 0),(Nat.eqb k 1);auto.
     apply M;now left.
 - unfold put;rewrite Dest;exact Mask.
Qed.
Definition bstate := ((nat->bounds)*(pointer->bounds))%type.
Definition bload (s:bstate) bases b d := match find(fun x=>Nat.eqb(fst x)b)bases with
 | Some(_,a)=>snd s(offset a d) | None=>Range 0 0 end.
Definition beffect j(s:bstate)e : bstate := match e with
 | Read r a=>(put(fst s)r(snd s a),snd s)
 | Write r a=>(fst s,fun k=>if ptr_eq k a then fst s r else snd s k)
 | Broadcast r n=>(put(fst s)r(Range n n),snd s)
 | ClearUpper=>(fun r=>if Nat.ltb r 16 && Nat.leb 2 j then Range 0 0 else fst s r,snd s)
 | Evaluate id bases=>(brun(bload s bases)(fragment_code add_cached_program id)(fst s),snd s) end.
Definition bmodels (b:bstate) s :=
 (forall r,bounded(fst b r)(registers s r)) /\ (forall a,bounded(snd b a)(cells s a)).
Definition singleton a n := (lower_bound a=?n)&&(upper_bound a=?n).
Lemma singleton_sound a n x : singleton a n=true ->bounded a x ->x=n.
Proof. unfold singleton,bounded;rewrite andb_true_iff,!Z.eqb_eq;intros[-> ->];lia. Qed.
Definition effect_ok(s:bstate)e := match e with
 | Evaluate id _=>singleton(fst s 29%nat)(radix-1) &&
   forallb legal_instruction(fragment_code add_cached_program id)
 | _=>true end.
Lemma beffect_sound j b s e : bmodels b s ->effect_ok b e=true ->
 bmodels(beffect j b e)(lane_effect j s e).
Proof.
 intros[R M]Ok;destruct e;split;intro i;cbn [beffect lane_effect Machine.execution.Lane.lane_effect fst snd registers cells];
 try(unfold put;destruct(Nat.eqb _ _));try(destruct(ptr_eq _ _));auto;
 try(unfold bounded;cbn;lia).
 - destruct(Nat.ltb i 16 && Nat.leb 2 j);auto;unfold bounded;cbn;lia.
 - apply andb_true_iff in Ok as[Mask Legal].
   apply brun_bounds;auto.
   + intros base disp Member;unfold bload,lane_load.
     destruct(find _ _)as[[reg a]|];auto;unfold bounded;cbn;lia.
   + eapply singleton_sound;eauto.
Qed.
Fixpoint bcheck j es b := match es with []=>true | e::tail=>effect_ok b e && bcheck j tail(beffect j b e) end.
Definition beffects j es b := fold_left(beffect j)es b.
Lemma beffects_sound j es b s : bcheck j es b=true ->bmodels b s ->
 bmodels(beffects j es b)(lane_effects j es s).
Proof.
 revert b s;induction es;intros b s C M;[exact M|].
 apply andb_true_iff in C as[E C];apply IHes;auto;now apply beffect_sound.
Qed.
Definition input_cell affine (a:pointer) :=
 ((Nat.eqb(fst a)point && (snd a<?1280)) ||
  (Nat.eqb(fst a)cached && (snd a<?cache_length affine))) &&
 (0<=?snd a) && (snd a mod 64=?0).
Definition input_limit (a:pointer) :=
 if Nat.eqb (fst a) point then cached_point_limit (Z.to_nat (snd a/64)) else split.
Definition initial_bounds affine : bstate :=
 (fun _=>Range 0(2^64-1),fun a=>Range 0(if input_cell affine a then input_limit a-1 else 2^64-1)).
Definition input_bounds affine s := forall a,input_cell affine a=true ->0<=cells s a<input_limit a.
Lemma initial_bounds_sound affine s : lane_words s ->input_bounds affine s ->bmodels(initial_bounds affine)s.
Proof.
 intros[W M]B;split;intro i;unfold bounded,initial_bounds;cbn [fst snd lower_bound upper_bound].
 - specialize(W i);unfold word64 in *;lia.
 - destruct(input_cell affine i)eqn:E;[specialize(B i E)|specialize(M i)];unfold word64 in *;lia.
Qed.
Theorem bounds_path_checked j full affine : bcheck j (expected_path full affine)(initial_bounds affine)=true.
Proof. destruct full,affine;vm_compute;reflexivity. Qed.
Definition prefix_state j full affine n s := lane_effects j(firstn n(expected_path full affine))s.
Definition prefix_bounds j full affine n := beffects j(firstn n(expected_path full affine))(initial_bounds affine).
Lemma bcheck_prefix j es b n : bcheck j es b=true ->bcheck j(firstn n es)b=true.
Proof. revert es b;induction n;intros[|e es]b H;cbn;auto.
 apply andb_true_iff in H as[E T];rewrite E;apply IHn;exact T. Qed.
Theorem prefix_sound j full affine n s : lane_words s ->input_bounds affine s ->
 bmodels(prefix_bounds j full affine n)(prefix_state j full affine n s).
Proof. intros W B;apply beffects_sound;[apply bcheck_prefix,bounds_path_checked|now apply initial_bounds_sound]. Qed.

Lemma prefix_segment j full affine n m s : (n<=m)%nat ->
 prefix_state j full affine m s=
 lane_effects j(skipn n(firstn m(expected_path full affine)))(prefix_state j full affine n s).
Proof.
 intro N;unfold prefix_state,lane_effects,Machine.execution.Lane.lane_effects.
 rewrite <-(firstn_skipn n(firstn m(expected_path full affine))) at 1.
 rewrite firstn_firstn,Nat.min_l by exact N;apply fold_left_app.
Qed.
