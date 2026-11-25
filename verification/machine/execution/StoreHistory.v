From Coq Require Import List ZArith.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch memory.WriteTrace.
Local Open Scope Z_scope.

(* The suffix is both the extension to the incoming log and the memory
   update between these two particular instruction boundaries. *)
Definition extends region p q:=exists ws,log q=log p++ws /\ confined region ws /\
 mem(machine q)=replay (mem(machine p)) ws.

Lemma compose region p q r : extends region p q -> extends region q r -> extends region p r.
Proof.
 intros [a [A [P M]]] [b [B [Q N]]];exists (a++b);split;[now rewrite B,A,app_assoc|].
 split;[now apply Forall_app|now rewrite replay_app,<-M,N].
Qed.
Lemma preserves region p q : extends region p q -> preserved (fun x=>~region x) (mem(machine p)) (mem(machine q)).
Proof. intros [ws [_ [S M]]] x O;rewrite M;apply (WriteTrace.frame _ _ S),O. Qed.
Lemma image region p q addr text : extends region p q -> mapped (mem(machine p)) addr text ->
 (forall x,addr<=x<addr+Z.of_nat(length text) -> ~region x) -> mapped (mem(machine q)) addr text.
Proof. intros [ws [_ [S ->]]] Code Sep;eapply keep_image;eassumption. Qed.
Lemma lend small large p q : (forall x,small x -> large x) -> extends small p q -> extends large p q.
Proof.
 intros Sub [ws [A [Safe M]]];exists ws;split;[exact A|split;[|exact M]].
 eapply Forall_impl;[|exact Safe];intros w H x X;apply Sub,(H x X).
Qed.
Lemma account e region p q : accounted e region p -> extends region p q -> accounted e region q.
Proof.
 intros Paid [ws [L [W M]]];destruct q as [pc s c logs];cbn [log machine] in L,M;subst logs;
 apply append_accounted;[exact Paid|exact W|intro x;now rewrite M].
Qed.
