From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks Instructions WordBounds.
Require Import Program FieldSpec Polynomial Interval Symbolic CachedAddABI Lane Control Kernels.
Import ListNotations. Open Scope Z_scope.
Definition bounded a z := lower a<=z<=upper a.
Lemma abstract_bounds s r e : (forall i,bounded(s i)(r i)) ->legal e=true ->
 bounded(abstract s e)(val r e).
Proof.
 intros S;induction e;cbn [legal abstract val];intro H;
 try apply andb_true_iff in H as[H1 H2];
 unfold bounded in *;cbn [lower upper] in *.
 - lia.
 - apply S.
 - specialize(IHe1 H1);specialize(IHe2 H2);lia.
 - apply product_bounds;auto.
 - specialize(IHe H1);apply Z.ltb_lt in H2;split;apply Z.div_le_mono;lia.
 - specialize(IHe H1);apply Z.ltb_lt in H2.
   destruct((0<=?lower(abstract s e))&&(upper(abstract s e)<?d))eqn:B.
   + apply andb_true_iff in B as[A B];apply Z.leb_le in A;apply Z.ltb_lt in B.
     rewrite Z.mod_small by lia;exact IHe.
   + cbn [lower upper];pose proof(Z.mod_pos_bound(val r e)d H2);lia.
Qed.
Definition forget a := I(C 0)(lower a)(upper a).
Fixpoint brun loads code s := match code with []=>s | (d,op)::tail=>
 brun loads tail(put s d(forget(aexec loads s d op))) end.
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
   change(bounded(aexec loads s d op)(bits load r d op)).
   rewrite rhs_ok by assumption;destruct op;cbn [aexec];try(apply abstract_bounds;assumption).
   + apply M;now left.
   + rewrite madd_value;apply abstract_bounds;[|destruct high;reflexivity].
     intro k;unfold madd_inputs;destruct(Nat.eqb k 0),(Nat.eqb k 1);auto.
     apply M;now left.
 - unfold put;rewrite Dest;exact Mask.
Qed.
Definition bstate := ((nat->interval)*(pointer->interval))%type.
Definition bload (s:bstate) bases b d := match find(fun x=>Nat.eqb(fst x)b)bases with
 | Some(_,a)=>snd s(offset a d) | None=>I(C 0)0 0 end.
Definition beffect j(s:bstate)e : bstate := match e with
 | Read r a=>(put(fst s)r(snd s a),snd s)
 | Write r a=>(fst s,fun k=>if ptr_eq k a then fst s r else snd s k)
 | Broadcast r n=>(put(fst s)r(I(C n)n n),snd s)
 | ClearUpper=>(fun r=>if Nat.ltb r 16 && Nat.leb 2 j then I(C 0)0 0 else fst s r,snd s)
 | Evaluate id bases=>(brun(bload s bases)(fragment_code add_cached_program id)(fst s),snd s) end.
Definition bmodels (b:bstate) s :=
 (forall r,bounded(fst b r)(registers s r)) /\ (forall a,bounded(snd b a)(cells s a)).
Definition singleton a n := (lower a=?n)&&(upper a=?n).
Lemma singleton_sound a n x : singleton a n=true ->bounded a x ->x=n.
Proof. unfold singleton,bounded;rewrite andb_true_iff,!Z.eqb_eq;intros[-> ->];lia. Qed.
Definition effect_ok(s:bstate)e := match e with
 | Evaluate id _=>singleton(fst s 29%nat)(radix-1) &&
   forallb legal_instruction(fragment_code add_cached_program id)
 | _=>true end.
Lemma beffect_sound j b s e : bmodels b s ->effect_ok b e=true ->
 bmodels(beffect j b e)(lane_effect j s e).
Proof.
 intros[R M]Ok;destruct e;split;intro i;cbn [beffect lane_effect fst snd registers cells];
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
Definition initial_bounds affine : bstate :=
 (fun _=>I(C 0)0(word-1),fun a=>I(C 0)0(if input_cell affine a then split-1 else word-1)).
Definition input_bounds affine s := forall a,input_cell affine a=true ->0<=cells s a<split.
Lemma initial_bounds_sound affine s : lane_words s ->input_bounds affine s ->bmodels(initial_bounds affine)s.
Proof.
 intros[W M]B;split;intro i;unfold bounded,initial_bounds;cbn [fst snd lower upper].
 - specialize(W i);unfold word,word64 in *;lia.
 - destruct(input_cell affine i)eqn:E;[specialize(B i E)|specialize(M i)];unfold word,word64 in *;lia.
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
 intro N;unfold prefix_state,lane_effects.
 rewrite <-(firstn_skipn n(firstn m(expected_path full affine))) at 1.
 rewrite firstn_firstn,Nat.min_l by exact N;apply fold_left_app.
Qed.
