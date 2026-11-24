From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordSemantics execution.WordBounds
  execution.ScalarBytes memory.WriteTrace.
From Machine Require execution.MappedFetch.
From Ed25519Simd.VerifyBatch Require Import Image Scatter Return.
Import ListNotations. Local Open Scope Z_scope.

(* Fetch each instruction from the same linked entry bytes used for the policy
   result. Offsets are relative to that entry at every load bias. *)
Definition empty_image text :=
 decode text=Some (3%nat,Test 6) /\
 decode (skipn 3 text)=Some (6%nat,Branch ScalarBytes.Equal (offset Empty-9)) /\
 decode (skipn (Z.to_nat (offset Empty)) text)=Some (5%nat,OneEax) /\
 decode (skipn (Z.to_nat (offset Empty+5)) text)=Some (1%nat,ScalarBytes.Ret).

Definition empty_trace origin text e :=
 let start c:=State (Running 0) e c in
 let '(ip,final):=empty_return e in
 let finish:=State (Returned ip) final (Some false) in
 forall carry,
 steps origin text (start carry) [] finish /\
 forall ws mid, steps origin text (start carry) ws mid ->
 ws=[] /\ steps origin text mid [] finish.

Lemma fetch_at o text off s c n op : 0<=off ->
 decode (skipn (Z.to_nat off) text)=Some (n,op) ->
 fetch o text (State (Running off) s c)=step o off n op s c.
Proof. intros O D;unfold fetch;cbn [loc cpu_state cf]. rewrite (proj2 (Z.ltb_ge _ _) O). now rewrite D. Qed.

Lemma empty_path_writes text : empty_image text -> forall o e,
 well_formed e -> count e=0%nat -> empty_trace o text e.
Proof.
 intros [Tested [Jump [One Ret]]] o e W EmptyCount.
 assert (N:regs e 6%nat=0).
 { unfold count in EmptyCount. pose proof (proj1 W 6%nat);unfold word64 in *;lia. }
 set (tested:=with_zf e true).
 destruct (empty_return e) as [ip final] eqn:E.
 unfold empty_trace;rewrite E;intros carry.
 assert (Run:steps o text (State (Running 0) e carry) [] (State (Returned ip) final (Some false))).
 { eapply advance with (ws:=[]) (tail:=[]) (mid:=State (Running 3) tested (Some false)).
   - rewrite (fetch_at o text 0 _ _ _ _ ltac:(lia) Tested);unfold step;rewrite N;reflexivity.
   - eapply advance with (ws:=[]) (tail:=[]) (mid:=State (Running (offset Empty)) tested (Some false)).
     + rewrite (fetch_at o text 3 _ _ _ _ ltac:(lia) Jump).
       change (Some (State (Running (9+(offset Empty-9))) tested (Some false),@nil WriteTrace.store)=Some (State (Running (offset Empty)) tested (Some false),@nil WriteTrace.store)).
       replace (9+(offset Empty-9)) with (offset Empty) by ring;reflexivity.
     + eapply advance with (ws:=[]) (tail:=[]) (mid:=State (Running (offset Empty+5)) (set tested 0 1) (Some false)).
       * rewrite (fetch_at o text (offset Empty) _ _ _ _ ltac:(change (0<=604);lia) One);reflexivity.
       * eapply advance with (ws:=[]) (tail:=[]);[|apply stop].
         rewrite (fetch_at o text (offset Empty+5) _ _ _ _ ltac:(change (0<=609);lia) Ret).
         cbn [step]. change (caller_step 0 0 Return (set tested 0 1)=(ip,final)) in E.
         rewrite E;reflexivity. }
 split;[exact Run|]. intros ws mid P.
 destruct(prefix_of_return _ _ _ _ _ Run ip eq_refl _ _ P) as [tail [Eq End]].
 symmetry in Eq;apply app_eq_nil in Eq as [-> ->];auto.
Qed.

(* In this version every instruction fetch observes the very memory that a
   store would update. A zero-length batch needs no disjointness premises. *)
Definition empty_mapped origin (text:list Z) e :=
 let '(ip,final):=empty_return e in
 let last:=State (Returned ip) final (Some false) in
 forall carry, let start:=State (Running 0) e carry in
 MappedFetch.steps origin (length text) start [] last /\
 forall ws mid, MappedFetch.steps origin (length text) start ws mid ->
 ws=[] /\ MappedFetch.steps origin (length text) mid [] last.

Lemma mapped_return origin text e : MappedFetch.mapped (mem e) origin text ->
 empty_trace origin text e -> empty_mapped origin text e.
Proof.
 intros Image Run;unfold empty_trace,empty_mapped in *.
 destruct (empty_return e) as [ip final];intro carry;destruct(Run carry) as [Full Every].
 set (start:=State (Running 0) e carry) in *.
 assert (All:forall ws mid, ScalarBytes.steps origin text start ws mid ->
   confined (fun _=>False) ws).
 { intros ws mid P;destruct(Every _ _ P) as [-> _];constructor. }
 pose proof (MappedFetch.same_prefixes origin text start _ Image (fun _ _ X=>X) All) as Both.
 split;[apply Both,Full|]. intros ws mid P;apply Both in P.
 destruct(Every _ _ P) as [-> Rest];split;[reflexivity|].
 assert (M:mem (cpu_state mid)=mem e) by exact (steps_memory _ _ _ _ _ P).
 apply (MappedFetch.same_prefixes origin text mid (fun _=>False));[now rewrite M|tauto| |exact Rest].
 intros xs last X;exact (All _ _ (MappedFetch.append_linked _ _ _ _ _ P _ _ X)).
Qed.
