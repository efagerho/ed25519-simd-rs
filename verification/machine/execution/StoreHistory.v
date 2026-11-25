From Coq Require Import List ZArith.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch memory.WriteTrace.
Local Open Scope Z_scope.

(* The suffix is both the extension to the incoming log and the memory
   update between these two particular instruction boundaries. *)
Definition extends region p q:=exists ws,log q=log p++ws /\ confined region ws /\
 forall x,mem(machine q) x=replay (mem(machine p)) ws x.

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
Lemma account e region p q : accounted e region p -> extends region p q -> accounted e region q.
Proof.
 intros Paid [ws [L [W M]]];destruct q as [pc s c logs];cbn [log machine] in L,M;subst logs;
 apply append_accounted;[exact Paid|exact W|exact M].
Qed.

(* The PC may be an in-symbol offset, a relative call target outside the
   symbol, or the absolute address popped by RET. *)
Lemma segment_checked region o text n p off t ws : ip p=o+off -> mapped (mem(machine p)) o text ->
 (forall x,o<=x<o+Z.of_nat(length text) -> ~region x) ->
 run n (ScalarBytes.fetch o text) (ScalarBytes.State (ScalarBytes.Running off) (machine p) (carry p))=Some(t,ws) ->
 confined region ws -> let q:=finish o p (t,ws) in
 segment o text n p=Some q /\ extends region p q.
Proof.
 intros PC Code Sep R Safe q;split.
 - unfold segment;rewrite PC;replace (o+off-o) with off by ring;now rewrite (run_lift _ _ _ _ _ _ _ R Safe Code Sep).
 - exists ws;split;[reflexivity|split;[exact Safe|intro x;exact (f_equal (fun m=>m x) (ScalarBytes.steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R)))]].
Qed.
