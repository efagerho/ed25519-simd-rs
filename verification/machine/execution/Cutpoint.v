From Coq Require Import List Bool ZArith Lia.
From Machine Require Import execution.WordSemantics execution.LinkedCalls execution.ScalarBytes execution.MappedFetch memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

(* Test the actual machine state at each boundary. Exhaustion and failed
   fetches both fail, including a failed fetch immediately before the exit. *)
Fixpoint until (fuel:nat) (at_exit:state->bool) (next:tick) s : option (state*list store) :=
 if at_exit s then Some (s,[]) else
 match fuel with
 | O => None
 | S k => match next s with
          | Some (mid,own) => option_map (fun '(t,tail) => (t,own++tail)) (until k at_exit next mid)
          | None => None end
 end.

Lemma sound fuel stop next : forall s t ws, until fuel stop next s=Some(t,ws) ->
 exists n, (n<=fuel)%nat /\ run n next s=Some(t,ws) /\ stop t=true.
Proof.
 induction fuel as [|fuel IH];intros s t ws H;cbn [until] in H;
 destruct (stop s) eqn:E;try discriminate;
 try solve [injection H as <- <-;exists 0%nat;split;[lia|auto]].
 destruct (next s) as [[mid own]|] eqn:F;[|discriminate].
 destruct (until fuel stop next mid) as [[last tail]|] eqn:R;[|discriminate].
 injection H as <- <-;destruct (IH _ _ _ R) as [n [B [Run End]]].
 exists (S n);split;[lia|split;[cbn [run];now rewrite F,Run|exact End]].
Qed.

(* At a terminal boundary every successful fixed-length execution ending
   there is the first hit. No assumption about the branch path is needed. *)
Lemma terminal_exact stop next (terminal:forall s,stop s=true -> next s=None) n :
 forall fuel s t ws, (n<=fuel)%nat -> run n next s=Some(t,ws) -> stop t=true ->
 until fuel stop next s=Some(t,ws).
Proof.
 induction n as [|n IH];intros fuel s t ws B R End.
 - injection R as <- <-;destruct fuel;cbn [until];now rewrite End.
 - destruct fuel as [|fuel];[lia|]. cbn [run] in R;cbn [until].
   destruct (stop s) eqn:E;[rewrite (terminal s E) in R;discriminate|].
   destruct (next s) as [[mid own]|] eqn:F;[|discriminate].
   destruct (run n next mid) as [[last tail]|] eqn:T;[|discriminate].
   injection R as <- <-;now rewrite (IH fuel _ _ _ ltac:(lia) T End).
Qed.

Definition outside size s := match loc s with
 | Returned _ => true
 | Running pc => (pc <? 0) || (Z.of_nat size <=? pc)
 end.

Lemma outside_terminal o size s : outside size s=true -> MappedFetch.fetch o size s=None.
Proof.
 destruct s as [[pc|ip] s c];[|reflexivity].
 unfold outside,MappedFetch.fetch,ScalarBytes.fetch;cbn [loc cpu_state].
 destruct (pc<?0);[reflexivity|]. cbn;intro Far;apply Z.leb_le in Far.
 rewrite skipn_all2;[reflexivity|].
 assert (L:forall m a k,length (snapshot m a k)=k).
 { intros m a k;revert a;induction k;cbn;auto. }
 rewrite L;lia.
Qed.

Lemma relocated_outside ip size delta :
 Z.of_nat size<2^32 -> -2^62<delta<2^62 -> (delta<0 \/ Z.of_nat size<=delta) ->
 forall t,loc t=Running (word(ip+delta)-ip) -> outside size t=true.
Proof.
 intros Size Fits Ext t PC;unfold outside;rewrite PC.
 destruct (word(ip+delta)-ip <? 0) eqn:N;[reflexivity|];apply Z.ltb_ge in N.
 cbn;apply Z.leb_le;destruct (Z_lt_ge_dec (word(ip+delta)-ip) (Z.of_nat size));[|lia].
 pose proof (small_relative ip delta (word(ip+delta)-ip) Fits ltac:(lia) eq_refl);lia.
Qed.

(* The existential run in a certificate and every successful prefix execute
   the same deterministic tick. Even a store of the previous value is charged. *)
Lemma terminal_prefix next n s t ws allowed :
 run n next s=Some(t,ws) -> next t=None -> confined allowed ws ->
 forall k mid pre, run k next s=Some(mid,pre) -> confined allowed pre.
Proof.
 revert s t ws;induction n as [|n IH];intros s t ws R End Safe [|k] mid pre P;
 try solve [injection P as <- <-;constructor].
 - injection R as <- <-;cbn [run] in P;rewrite End in P;discriminate.
 - cbn [run] in R,P;destruct (next s) as [[u own]|];[|discriminate].
   destruct (run n next u) as [[last tail]|] eqn:T;[|discriminate].
   destruct (run k next u) as [[v rest]|] eqn:F;[|discriminate].
   injection R as <- <-;injection P as <- <-;apply Forall_app in Safe as [A B].
   apply Forall_app;split;[exact A|eapply IH;eassumption].
Qed.

Definition verified_exit o size fuel s allowed (post:state->Prop) :=
 let next:=MappedFetch.fetch o size in
 exists t ws, until fuel (outside size) next s=Some(t,ws) /\ post t /\ confined allowed ws /\
 mem(cpu_state t)=replay (mem(cpu_state s)) ws /\
 forall k mid pre, run k next s=Some(mid,pre) -> confined allowed pre.

Theorem exit_checked o text fuel s t ws allowed (post:state->Prop) n :
 run n (ScalarBytes.fetch o text) s=Some(t,ws) -> confined allowed ws -> post t ->
 mapped (mem(cpu_state s)) o text -> (forall x,o<=x<o+Z.of_nat(length text) -> ~allowed x) ->
 (n<=fuel)%nat -> outside (length text) t=true ->
 verified_exit o (length text) fuel s allowed post.
Proof.
 intros R W Post Image Apart B End.
 pose proof (run_lift _ _ _ _ _ _ _ R W Image Apart) as M.
 exists t,ws;split;[exact (terminal_exact _ _ (outside_terminal _ _) _ _ _ _ _ B M End)|].
 split;[exact Post|split;[exact W|split]].
 - exact (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R)).
 - eapply terminal_prefix;[exact M|apply outside_terminal,End|exact W].
Qed.

(* Compose checked segments while keeping the writer PC, address and payload
   of each instruction in execution order. *)
Definition path next allowed n s t ws :=
 run n next s=Some(t,ws) /\ confined allowed ws.

Lemma join next allowed n k s mid t xs ys :
 path next allowed n s mid xs -> path next allowed k mid t ys ->
 path next allowed (n+k) s t (xs++ys).
Proof.
 intros [First X] [Last Y];split;[eapply run_append;eassumption|now apply Forall_app].
Qed.

Lemma mapped_path o text allowed n s t ws :
 path (ScalarBytes.fetch o text) allowed n s t ws ->
 mapped (mem(cpu_state s)) o text -> (forall x,o<=x<o+Z.of_nat(length text) -> ~allowed x) ->
 path (MappedFetch.fetch o (length text)) allowed n s t ws /\ mapped (mem(cpu_state t)) o text.
Proof.
 intros [R W] Image Apart;split;[split;[eapply run_lift;eassumption|exact W]|].
 rewrite (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R));eapply keep_image;eassumption.
Qed.

Arguments join {next allowed n k s mid t xs ys} _ _.
Arguments mapped_path {o text allowed n s t ws} _ _ _.
