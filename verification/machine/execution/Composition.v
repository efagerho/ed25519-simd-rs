(* A phase can have several outcomes, for example when a callee leaves
   volatile registers unspecified. A caller must handle every outcome. *)
Definition ensures {A : Type} (run post : A -> Prop) :=
  (exists x, run x) /\ forall x, run x -> post x.

Definition followed_by {A B : Type} (first : A -> Prop) (next : A -> B -> Prop) y :=
  exists x, first x /\ next x y.

Lemma sequence {A B : Type} (first middle : A -> Prop) (next : A -> B -> Prop) post :
  ensures first middle ->
  (forall x, middle x -> ensures (next x) post) ->
  ensures (followed_by first next) post.
Proof.
  intros [[x X] All] Next. split.
  - destruct (proj1 (Next x (All x X))) as [y Y]. exists y, x. auto.
  - intros y [a [Ate N]]. exact (proj2 (Next a (All a Ate)) y N).
Qed.

Lemma observations {A : Type} (run : A -> Prop) :
  (exists x, run x) -> ensures run run.
Proof. intro Progress. split; [exact Progress|auto]. Qed.

Definition output {A : Type} (step : option A) x := step = Some x.

Lemma option_result {A : Type} (step : option A) post :
  (exists x, step = Some x /\ post x) -> ensures (output step) post.
Proof.
  intros [x [Run P]]. split; [now exists x|].
  intros y R. unfold output in R. rewrite Run in R. now injection R as <-.
Qed.

(* A proved deterministic step fixes the state passed to its continuation. *)
Lemma after_some {A B : Type} {step : option A} {x : A} {next : A -> B -> Prop} {post} :
  step = Some x -> ensures (next x) post -> ensures (followed_by (output step) next) post.
Proof.
  intros Step Rest. apply sequence with (middle := fun y => x = y).
  - apply option_result. exists x; auto.
  - intros y <-. exact Rest.
Qed.

Lemma consequence {A : Type} {run before after : A -> Prop} :
  ensures run before -> (forall x, run x -> before x -> after x) -> ensures run after.
Proof. intros [One All] Change. split; [exact One|intros x X; exact (Change x X (All x X))]. Qed.

(* One input witnesses progress; the continuation proof covers every input. *)
Definition with_input {I A : Type} (run : I -> A -> Prop) y := exists i, run i y.

Lemma each_input {I A : Type} (witness : I) {run : I -> A -> Prop} {post} :
  (forall i, ensures (run i) post) -> ensures (with_input run) post.
Proof.
  intro All. split.
  - destruct (proj1 (All witness)) as [y Run]. now exists y,witness.
  - intros y [i Run]. exact (proj2 (All i) y Run).
Qed.
