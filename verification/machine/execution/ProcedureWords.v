From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarWords execution.VectorProcedure execution.WordBounds.

Definition words (f:procedure):=forall p q,well_formed(machine p) -> f p=Some q -> well_formed(machine q).
Lemma sequence f g : words f -> words g -> words(then_run f g).
Proof. intros F G p q W;unfold then_run;destruct(f p) eqn:R;[now apply G,(F _ _ W R)|discriminate]. Qed.
Lemma block base text n : words(segment base text n).
Proof. exact (segment_wf base text n). Qed.
Lemma call base text retbase rettext f : words f -> words(wrapped base text retbase rettext f).
Proof. intro F;change (words(then_run (segment base text 1) (then_run f (segment retbase rettext 1))));
 apply sequence;[apply block|apply sequence;[exact F|apply block]]. Qed.
