From Coq Require Import List ZArith Bool Lia Ring.
From Machine Require Import Blocks Instructions WordBounds.
Require Import Program FieldSpec Polynomial Interval ScalarSpec ScalarMath Symbolic.
Import ListNotations. Open Scope Z_scope.

Definition code i := firstn 13(skipn(1+13*i)(fragment_code scalar_program 7)).
Definition bound i := 2^(Z.of_nat i+4)*B.
Definition constants i := match i with
 | 26%nat=>Some(B-1) | 27%nat=>Some l4 | 28%nat=>Some l0
 | 29%nat=>Some l1 | 30%nat=>Some l2 | 31%nat=>Some factor | _=>None end.
Definition initial n i := match constants i with
 | Some c=>I(C c)c c | None=>I(V i)0(if Nat.ltb i 26 then bound n-1 else W-1) end.
Definition no_loads (_:nat)(_:Z) := I(C 0)0 0.
Definition result n := arun no_loads(code n)(initial n).
Definition constants_ok r := forall i c,constants i=Some c ->r i=c.
Definition bounded_state n r := forall i,(i<26)%nat ->0<=r i<bound n.
Definition remaining i r := r 23%nat+
 number B(map(fun k=>r k+B*r(9+k)%nat)(seq i(9-i))).
Definition remainingE i s := Plus(s 23%nat)
 (numberE B(map(fun k=>Plus(s k)(Times(C B)(s(9+k)%nat)))(seq i(9-i)))).
Definition sub a b := Plus a(Times(C(-1))b).
Definition xE n := Plus(V n)(V 23).
Definition qE n := term(result n(18+n)%nat).
Definition correction n := sub(sub
 (Times(C B)(Quot(Plus(xE n)(C(B-1)))B))(xE n))
 (Rem(Times(qE n)(C l0))B).
Definition identity n := sub(sub(Times(C B)(remainingE(S n)(fun i=>term(result n i))))
 (remainingE n V))(Times(qE n)(C L)).
Definition step_check n :=
 check no_loads(code n)(initial n) && equal_expr(identity n)(correction n) &&
 equal_expr(qE n)(Rem(Times(Rem(xE n)B)(C factor))B) &&
 forallb(fun i=>(0<=?lower(result n i))&&(upper(result n i)<?bound(S n)))(seq 0 26) &&
 forallb(fun i=>match constants i with Some c=>singleton(result n i)c | None=>true end)(seq 26 6).
Theorem steps_checked : forallb step_check(seq 0 5)=true.
Proof. vm_compute;reflexivity. Qed.

Lemma code_loads n : (n<5)%nat ->loads_of(code n)=[].
Proof. intro H;do 5(destruct n as[|n];[vm_compute;reflexivity|]);lia. Qed.
Lemma initial_models n r : (forall i,word64(r i)) ->constants_ok r ->bounded_state n r ->
 forall i,models r(initial n i)(r i).
Proof.
 intros Words Const Bound i;unfold initial;destruct(constants i)as[c|]eqn:C.
 - rewrite(Const _ _ C);unfold models;cbn [val term lower upper];split;[reflexivity|lia].
 - unfold models;cbn [val term lower upper];split;[reflexivity|].
   destruct(Nat.ltb i 26)eqn:E.
   + apply Nat.ltb_lt in E;specialize(Bound i E);lia.
   + specialize(Words i);unfold word64,W in *;lia.
Qed.
Lemma remainingE_value env s r i : (forall k,val env(s k)=r k) ->
 val env(remainingE i s)=remaining i r.
Proof.
 intro H;unfold remainingE,remaining;cbn [val];rewrite H,numberE_sound.
 f_equal;f_equal;rewrite map_map;apply map_ext;intro k;cbn [val];now rewrite !H.
Qed.
Local Opaque code result bound.
Theorem step_correct n load r : (n<5)%nat ->
 (forall i,word64(r i)) ->constants_ok r ->bounded_state n r ->
 let after:=run load(code n)r in
 constants_ok after /\ bounded_state(S n)after /\
 0<=after(18+n)%nat<B /\
 B*remaining(S n)after=remaining n r+after(18+n)%nat*L.
Proof.
 intros N Words Const Bound after.
 pose proof steps_checked as Check;rewrite forallb_forall in Check.
 specialize(Check n ltac:(apply in_seq;lia));unfold step_check in Check.
 apply andb_true_iff in Check as[Check Saved].
 apply andb_true_iff in Check as[Check Bounds].
 apply andb_true_iff in Check as[Check Qeq].
 apply andb_true_iff in Check as[Legal Eq].
 pose proof(run_ok r no_loads load(code n)(initial n)r
  ltac:(intros b d I;rewrite code_loads in I by exact N;contradiction)
  (initial_models n r Words Const Bound)Legal)as Model.
 change(forall i,models r(result n i)(after i))in Model.
 assert(Q:after(18+n)%nat=quotient(r n+r 23%nat)).
 { apply(equal_expr_sound r)in Qeq;unfold qE,xE in Qeq;cbn [val]in Qeq.
   rewrite(proj1(Model(18+n)%nat))in Qeq;exact Qeq. }
 split.
 - intros i c C;rewrite forallb_forall in Saved.
   assert(I:In i(seq 26 6)).
   { unfold constants in C;do 32(destruct i as[|i];[try discriminate;apply in_seq;lia|]);discriminate. }
   specialize(Saved i I);rewrite C in Saved;eapply singleton_sound;eauto.
 - split.
   + intros i I;rewrite forallb_forall in Bounds;specialize(Bounds i ltac:(apply in_seq;lia)).
     apply andb_true_iff in Bounds as[A Z];apply Z.leb_le in A;apply Z.ltb_lt in Z.
     destruct(Model i)as[_ M];lia.
   + split;[rewrite Q;apply quotient_bound|].
     apply(equal_expr_sound r)in Eq;unfold identity,correction,sub in Eq.
     cbn [val]in Eq.
     rewrite(remainingE_value r (fun i=>term(result n i))after(S n)
       (fun i=>proj1(Model i)))in Eq.
     rewrite(remainingE_value r V r n ltac:(intro;reflexivity))in Eq.
     unfold qE,xE in Eq;cbn [val]in Eq;rewrite(proj1(Model(18+n)%nat))in Eq.
     pose proof(Bound n ltac:(lia))as A;pose proof(Bound 23%nat ltac:(lia))as D.
     pose proof(low_carry(r n+r 23%nat)ltac:(lia))as Carry.
     rewrite <-Q in Carry.
     replace(r n+r 23%nat+(B-1))with(r n+r 23%nat+B-1)in Eq by ring.
     rewrite Carry in Eq;lia.
Qed.
