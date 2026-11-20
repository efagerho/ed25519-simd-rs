From ProofArithmetic Require Import Interval Polynomial.
From Coq Require Import List ZArith Bool Lia Ring.
From Machine Require Import Blocks Instructions WordBounds.
From Ed25519Simd.Scalar Require Import Program ScalarSpec ScalarMath Symbolic Product Reduction.
Import ListNotations. Open Scope Z_scope.
Fixpoint reduce n load r := match n with O=>r | S i=>run load(Reduction.code i)(reduce i load r)end.
Lemma reduce_correct n load r : (n<=5)%nat ->
 (forall b d,word64(load b d)) ->(forall i,word64(r i)) ->
 constants_ok r ->bounded_state 0 r ->
 constants_ok(reduce n load r) /\ bounded_state n(reduce n load r) /\
 (exists q,0<=q<B^Z.of_nat n /\
 B^Z.of_nat n*remaining n(reduce n load r)=remaining 0 r+q*L).
Proof.
 intros N Load Words Const Bound;induction n as[|n IH].
 - cbn [reduce];split;[exact Const|split;[exact Bound|]]. exists 0;change(0<=0<1 /\ 1*remaining 0 r=remaining 0 r+0*L);split;[lia|ring].
 - destruct(IH ltac:(lia))as[C [D [q [Q E]]]].
   assert(Words':forall i,word64(reduce n load r i)).
   { clear N IH C D q Q E;induction n;cbn [reduce];[exact Words|apply run_words;assumption]. }
   destruct(step_correct n load(reduce n load r)ltac:(lia)Words' C D)as[C' [D' [Q' E']]].
   cbn [reduce];split;[exact C'|split;[exact D'|]].
   exists(q+B^Z.of_nat n*run load(Reduction.code n)(reduce n load r)(18+n)%nat).
   rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia.
   pose proof(Z.pow_pos_nonneg B (Z.of_nat n) B_positive ltac:(lia));split;nia.
Qed.
Definition normalize_code := firstn 17(skipn 66(fragment_code scalar_program 7)).
Definition normalize_result := arun Reduction.no_loads normalize_code(Reduction.initial 5).
Definition normalize_check := check Reduction.no_loads normalize_code(Reduction.initial 5) &&
 equal_expr(Product.packE(fun i=>term(normalize_result i))0)(remainingE 5 V) &&
 forallb(fun i=>(0<=?lower(normalize_result i))&&(upper(normalize_result i)<?B))(seq 0 4) &&
 (0<=?lower(normalize_result 4)).
Theorem normalize_checked : normalize_check=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque normalize_code normalize_result.
Theorem normalize_correct load r : (forall i,word64(r i)) ->constants_ok r ->bounded_state 5 r ->
 let after:=run load normalize_code r in
 Product.pack after 0=remaining 5 r /\
 (forall i,(i<4)%nat->0<=after i<B) /\ 0<=after 4%nat.
Proof.
 intros Words Const Bound after;pose proof normalize_checked as Check;unfold normalize_check in Check.
 apply andb_true_iff in Check as[Check Top];apply andb_true_iff in Check as[Check Bounds];
 apply andb_true_iff in Check as[Legal Eq].
 pose proof(run_ok r Reduction.no_loads load normalize_code(Reduction.initial 5)r
 ltac:(intros b d I;change(In(b,d)[])in I;contradiction)
 (initial_models 5 r Words Const Bound)Legal)as Model.
 change(forall i,models r(normalize_result i)(after i))in Model.
 split.
 - apply(equal_expr_sound r)in Eq;rewrite(remainingE_value r V r 5 ltac:(intro;reflexivity))in Eq.
   unfold packE in Eq;rewrite numberE_sound in Eq;unfold pack;cbn [seq map val]in Eq|-*.
   now rewrite !(fun i=>proj1(Model i))in Eq.
 - split.
   + intros i I;rewrite forallb_forall in Bounds;specialize(Bounds i ltac:(apply in_seq;lia)).
     apply andb_true_iff in Bounds as[A Z];apply Z.leb_le in A;apply Z.ltb_lt in Z;destruct(Model i)as[_ M];lia.
   + apply Z.leb_le in Top;destruct(Model 4%nat)as[_ M];lia.
Qed.
