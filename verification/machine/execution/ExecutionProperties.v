From Coq Require Import ZArith List Bool.
From Machine Require Import execution.Blocks.
Import ListNotations.

(* The two memory views have different permissions. A store updates one
   vector cell. A near call writes one return-address slot. *)
Lemma ptr_eq_true a b : ptr_eq a b = true -> a = b.
Proof.
 destruct a as [r x], b as [s y]; unfold ptr_eq; cbn.
 rewrite andb_true_iff, Nat.eqb_eq, Z.eqb_eq. intros [-> ->]; reflexivity.
Qed.

Definition permitted_write l e := match e with
 | Write _ a => vector_ok l a true = true | _ => True end.

Lemma op_writes p l c op mid es :
 exec_op p l c op = Some (mid,es) ->
 Forall (permitted_write l) es /\ return_memory mid = return_memory c.
Proof.
 destruct op; cbn [exec_op]; repeat match goal with
 | |- context [match ?v with _ => _ end] => destruct v eqn:?
 end; intro H; try discriminate; inversion H; subst;
 split; try reflexivity; repeat constructor; assumption.
Qed.

Lemma body_writes p l c ops mid es :
 exec_body p l c ops = Some (mid,es) ->
 Forall (permitted_write l) es /\ return_memory mid = return_memory c.
Proof.
 revert c mid es; induction ops as [|op rest IH]; intros c mid es H; cbn in H.
 - inversion H; subst; split; constructor.
 - destruct (exec_op p l c op) as [[next head]|] eqn:O; try discriminate.
   destruct (exec_body p l next rest) as [[last tail]|] eqn:B; try discriminate.
   inversion H; subst. destruct (op_writes _ _ _ _ _ _ O) as [A R].
   destruct (IH _ _ _ B) as [T S]. split; [now apply Forall_app|congruence].
Qed.

Lemma effects_frame p l es d a :
 vector_ok l a true = false -> Forall (permitted_write l) es ->
 memory (effects p es d) a = memory d a.
Proof.
 intros P W. revert d. induction W as [|e es W Ws IH]; intro d; [reflexivity|].
 change (memory (effects p es (apply_effect p d e)) a = memory d a). rewrite IH.
 destruct e; try reflexivity. cbn [apply_effect memory].
 destruct (ptr_eq a a0) eqn:E; [|reflexivity].
 apply ptr_eq_true in E; subst. unfold permitted_write in W. congruence.
Qed.

Lemma transfer_frame l c next e last a :
 return_ok l a = false -> transfer l c next e = Some last ->
 return_memory last a = return_memory c a.
Proof.
 intros P. destruct e; unfold transfer, transfer_recorded; cbn beta iota zeta; repeat match goal with
 | |- context [match ?v with _ => _ end] => destruct v eqn:?
 end; intro H; try discriminate; inversion H; subst; try reflexivity.
 all: cbn in *; try congruence.
 all: match goal with |- context[ptr_eq ?x ?y] => destruct (ptr_eq x y) eqn:E end; [|reflexivity].
 all: apply ptr_eq_true in E; subst; congruence.
Qed.

Theorem step_memory_frame p l s t :
 step p l s = Some t -> forall a,
 (vector_ok l a true = false -> memory (snd t) a = memory (snd s) a) /\
 (return_ok l a = false -> return_memory (fst t) a = return_memory (fst s) a).
Proof.
 destruct s as [c d]. unfold step, dispatch. cbn [fst snd].
 destruct (rip c) as [pc | | saved]; try discriminate.
 destruct (lookup (sections p) pc) as [b|]; [|discriminate].
 unfold block_control. destruct (exec_body p l c (body b)) as [[mid es]|] eqn:B; [|discriminate].
 destruct (transfer l mid (after p b) (terminator b)) as [last|] eqn:T; [|discriminate].
 intros [= <-] a. cbn [fst snd].
 destruct (body_writes _ _ _ _ _ _ B) as [W R]. split.
 - intro P. eapply effects_frame; eassumption.
 - intro P. rewrite <-R. eapply transfer_frame; eassumption.
Qed.

Theorem execution_memory_frame p l s t :
 reaches p l s t -> forall a,
 (vector_ok l a true = false -> memory (snd t) a = memory (snd s) a) /\
 (return_ok l a = false -> return_memory (fst t) a = return_memory (fst s) a).
Proof.
 intro R; induction R as [s|s t u S R IH]; intro a; [split; reflexivity|].
 destruct (step_memory_frame _ _ _ _ S a) as [V Rm], (IH a) as [Vs Rs].
 split; intro P; [now rewrite Vs, V | now rewrite Rs, Rm].
Qed.

(* A trace lists the incoming control states of successive successful block
   steps. Each contains the PC, GPRs, ZF, and return-address memory. *)
Inductive control_trace p l : state -> list control -> state -> Prop :=
| trace_done s : control_trace p l s [] s
| trace_step s t u tail : step p l s = Some t -> control_trace p l t tail u ->
    control_trace p l s (fst s :: tail) u.

Theorem control_trace_independent p l s trace t :
 control_trace p l s trace t -> forall d,
 exists final_data, control_trace p l (fst s,d) trace (fst t,final_data).
Proof.
 intro T. induction T as [s|s t u tail S T IH]; intro d.
 - exists d. constructor.
 - unfold step in S. destruct (dispatch p l (fst s)) as [[next es]|] eqn:D; [|discriminate].
   inversion S; subst t. destruct (IH (effects p es d)) as [final_data H].
   exists final_data. apply (trace_step _ _ (fst s,d) (next,effects p es d));
   [unfold step; cbn [fst snd]; now rewrite D | exact H].
Qed.

Theorem reaches_has_trace p l s t :
 reaches p l s t <-> exists cs, control_trace p l s cs t.
Proof.
 split.
 - intro R; induction R as [s|s t u S R [cs T]].
   + exists []; constructor.
   + exists (fst s :: cs). econstructor; eassumption.
 - intros [cs T]; induction T; [constructor|eapply more; eassumption].
Qed.

Theorem step_failure_independent p l c d1 d2 :
 step p l (c,d1) = None <-> step p l (c,d2) = None.
Proof.
 unfold step; cbn [fst snd]. destruct (dispatch p l c) as [[next es]|]; cbn [apply_result]; split; congruence.
Qed.
