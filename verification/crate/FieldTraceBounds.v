From ProofArithmetic Require Import Ranges.
From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.Blocks isa.Instructions execution.WordBounds.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Curve25519 Require Import FieldPolynomial.
From Ed25519Simd Require Import FieldSymbolic.
From Machine Require Import execution.Lane.
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
Section Trace.
Variable p : program.
Definition beffect j(s:bstate)e : bstate := match e with
 | Read r a=>(put(fst s)r(snd s a),snd s)
 | Write r a=>(fst s,fun k=>if ptr_eq k a then fst s r else snd s k)
 | Broadcast r n=>(put(fst s)r(Range n n),snd s)
 | ClearUpper=>(fun r=>if Nat.ltb r 16 && Nat.leb 2 j then Range 0 0 else fst s r,snd s)
 | Evaluate id bases=>(brun(bload s bases)(fragment_code p id)(fst s),snd s) end.
Definition bmodels (b:bstate) s :=
 (forall r,bounded(fst b r)(registers s r)) /\ (forall a,bounded(snd b a)(cells s a)).
Definition singleton a n := (lower_bound a=?n)&&(upper_bound a=?n).
Lemma singleton_sound a n x : singleton a n=true ->bounded a x ->x=n.
Proof. unfold singleton,bounded;rewrite andb_true_iff,!Z.eqb_eq;intros[-> ->];lia. Qed.
Definition effect_ok(s:bstate)e := match e with
 | Evaluate id _=>singleton(fst s 29%nat)(radix-1) &&
   forallb legal_instruction(fragment_code p id)
 | _=>true end.
Lemma beffect_sound j b s e : bmodels b s ->effect_ok b e=true ->
 bmodels(beffect j b e)(lane_effect p j s e).
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
 bmodels(beffects j es b)(lane_effects p j es s).
Proof.
 revert b s;induction es;intros b s C M;[exact M|].
 apply andb_true_iff in C as[E C];apply IHes;auto;now apply beffect_sound.
Qed.
End Trace.

Definition includes a lo hi := (lo<=?lower_bound a)&&(upper_bound a<=?hi).
Lemma includes_sound a lo hi x : includes a lo hi=true ->bounded a x ->lo<=x<=hi.
Proof. unfold includes,bounded;rewrite andb_true_iff,!Z.leb_le;lia. Qed.
