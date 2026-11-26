From Coq Require Import List ZArith.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch memory.WriteTrace.
Local Open Scope Z_scope.

Definition extends := LinkedRun.extends_log.

Lemma compose region p q r : extends region p q -> extends region q r -> extends region p r.
Proof.
 intros [a [A [P M]]] [b [B [Q N]]];exists (a++b);split;[now rewrite B,A,app_assoc|].
 split;[now apply Forall_app|intro x;rewrite N,replay_app;apply replay_equal,M].
Qed.
Lemma preserves region p q : extends region p q -> preserved (fun x=>~region x) (mem(machine p)) (mem(machine q)).
Proof. intros [ws [_ [S M]]] x O;rewrite M;apply (WriteTrace.frame _ _ S),O. Qed.
Lemma image region p q addr text : extends region p q -> mapped (mem(machine p)) addr text ->
 (forall x,addr<=x<addr+Z.of_nat(length text) -> ~region x) -> mapped (mem(machine q)) addr text.
Proof. intros [ws [_ [S M]]] Code Sep i I;rewrite M;apply (keep_image _ _ _ _ _ Code Sep S i I). Qed.
Lemma lend small large p q : (forall x,small x -> large x) -> extends small p q -> extends large p q.
Proof.
 intros Sub [ws [A [Safe M]]];exists ws;split;[exact A|split;[|exact M]].
 eapply Forall_impl;[|exact Safe];intros w H x X;apply Sub,(H x X).
Qed.
Definition account := LinkedRun.account_history.
Definition segment_checked := LinkedRun.segment_history.

(* A callee can check its entire write history in a fresh cursor. Rejoining
   the caller keeps those same events and the callee's actual machine state. *)
Definition fresh p:=initial (ip p) (machine p) (carry p).
Definition rejoin p t:=Cursor (ip t) (machine t) (carry t) (log p++log t).
Lemma rejoin_history region p t : accounted (machine p) region t -> extends region p (rejoin p t).
Proof. intros [Safe Mem];exists (log t);auto. Qed.
