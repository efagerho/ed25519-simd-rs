From Coq Require Import List ZArith Lia.
From Machine Require Import execution.WordSemantics execution.LinkedCalls execution.ScalarBytes
 execution.MappedFetch memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

(* Cross a symbol boundary with the CPU that actually reached it. CALL and
   nested RET both supply the next absolute PC. The caller can resume at any
   instruction in its text, including a return address read from memory. *)
Record cursor := Cursor { ip:Z; machine:cpu; carry:option bool; log:list store }.
Definition initial ip s c := Cursor ip s c [].
Definition absolute origin s := match loc s with Running off=>origin+off | Returned addr=>addr end.
Definition finish origin prior (r:state*list store) :=
 let '(s,ws):=r in Cursor (absolute origin s) (cpu_state s) (cf s) (log prior++ws).
Definition segment origin (text:list Z) n prior :=
 option_map (finish origin prior)
   (run n (MappedFetch.fetch origin (length text))
      (State (Running (ip prior-origin)) (machine prior) (carry prior))).
Definition bind {A B} (x:option A) (f:A->option B) := match x with Some a=>f a |None=>None end.

Definition accounted (entry:cpu) (allowed:Z->Prop) p :=
 confined allowed (log p) /\ forall x,mem (machine p) x=WriteTrace.replay (mem entry) (log p) x.
Lemma initial_accounted e allowed start c : accounted e allowed (initial start e c).
Proof. split;[constructor|reflexivity]. Qed.

Lemma replay_equal m m' ws : (forall x,m x=m' x) ->
 forall x,WriteTrace.replay m ws x=WriteTrace.replay m' ws x.
Proof.
 revert m m';induction ws as [|w ws IH];intros m m' E x;[apply E|].
 apply IH;intro y;unfold commit,FlatMemory.write_bytes;destruct (_ && _)%bool;auto.
Qed.
Lemma append_accounted e allowed p pc s c ws : accounted e allowed p -> confined allowed ws ->
 (forall x,mem s x=WriteTrace.replay (mem (machine p)) ws x) ->
 accounted e allowed (Cursor pc s c (log p++ws)).
Proof.
 intros [W M] S F;split;[apply Forall_app;auto|].
 intro x;cbn [log machine];rewrite replay_app,F;apply replay_equal,M.
Qed.

Lemma at_segment e allowed p origin text n off s ws : accounted e allowed p ->
 ip p=origin+off -> MappedFetch.mapped (mem (machine p)) origin text ->
 (forall x,origin<=x<origin+Z.of_nat(length text)->~allowed x) ->
 run n (ScalarBytes.fetch origin text) (State (Running off) (machine p) (carry p))=Some(s,ws) ->
 confined allowed ws ->
 segment origin text n p=Some(finish origin p (s,ws)) /\ accounted e allowed (finish origin p (s,ws)).
Proof.
 intros Prev At M Apart R Safe;split.
 - unfold segment;rewrite At;replace (origin+off-origin) with off by ring.
   now rewrite (run_lift _ _ _ _ _ _ _ R Safe M Apart).
 - apply append_accounted;[exact Prev|exact Safe|].
   intro x;rewrite (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R));reflexivity.
Qed.
Lemma image_after e allowed p origin text : accounted e allowed p -> mapped (mem e) origin text ->
 (forall x,origin<=x<origin+Z.of_nat(length text)->~allowed x) -> mapped (mem(machine p)) origin text.
Proof. intros [W M] Code Sep i I;rewrite M;exact (keep_image _ _ _ _ _ Code Sep W i I). Qed.

(* Stop on the first RET. A step at a running PC that cannot be decoded
   still fails. The fuel counts instructions, including RET itself. *)
Fixpoint until_return (fuel:nat) (next:tick) (s:state) : option (state*list store) :=
 match loc s with
 | Returned _=>Some(s,[])
 | Running _=>match fuel with
   | O=>None
   | S rest=>match next s with
     | Some(mid,own)=>option_map (fun '(t,tail)=>(t,own++tail)) (until_return rest next mid)
     | None=>None end end end.

Lemma until_exact origin size k : forall fuel s t ws back, (k<=fuel)%nat ->
 run k (MappedFetch.fetch origin size) s=Some(t,ws) -> loc t=Returned back ->
 until_return fuel (MappedFetch.fetch origin size) s=Some(t,ws).
Proof.
 induction k as [|k IH];intros fuel s t ws back Bound R Ret.
 - cbn [run] in R;injection R as <- <-;destruct fuel;cbn [until_return];now rewrite Ret.
 - destruct fuel as [|fuel];[lia|]. destruct s as [[off|ip] s c];[|discriminate].
   cbn [run] in R;destruct (MappedFetch.fetch origin size (State (Running off) s c)) as [[mid own]|] eqn:F;
     [|discriminate]. destruct (run k _ mid) as [[last tail]|] eqn:T;[|discriminate].
   injection R as <- <-;cbn [until_return loc];rewrite F,(IH fuel _ _ _ back ltac:(lia) T Ret);reflexivity.
Qed.

Definition returning origin size fuel p :=
 option_map (finish origin p)
  (until_return fuel (MappedFetch.fetch origin size)
   (State (Running (ip p-origin)) (machine p) (carry p))).

(* Memory and store events come from the same fetched instructions even if
   the input did not satisfy a routine's calling convention. *)
Lemma fetched_memory origin size s t ws : MappedFetch.fetch origin size s=Some(t,ws) ->
 mem(cpu_state t)=WriteTrace.replay (mem(cpu_state s)) ws.
Proof.
 intro F;unfold MappedFetch.fetch in F.
 apply (steps_memory origin (snapshot (mem(cpu_state s)) origin size) s).
 rewrite <- (app_nil_r ws) at 1;eapply ScalarBytes.advance;[exact F|constructor].
Qed.

Section Memory.
Variables (origin:Z) (size:nat).
Local Notation tick := (MappedFetch.fetch origin size).
Lemma run_memory n : forall s t ws,run n tick s=Some(t,ws) ->
 mem(cpu_state t)=WriteTrace.replay (mem(cpu_state s)) ws.
Proof.
 induction n as [|n IH];intros s t ws R;[injection R as <- <-;reflexivity|].
 cbn [run] in R;destruct(tick s) as [[u head]|] eqn:F;[|discriminate].
 destruct(run n tick u) as [[last tail]|] eqn:T;[|discriminate].
 injection R as <- <-;rewrite replay_app,<-(fetched_memory _ _ _ _ _ F);exact (IH _ _ _ T).
Qed.

Lemma returned_run fuel : forall s t ws,until_return fuel tick s=Some(t,ws) ->
 exists n back, (n<=fuel)%nat /\ run n tick s=Some(t,ws) /\ loc t=Returned back.
Proof.
 induction fuel as [|fuel IH];intros [[off|back] s c] t ws R;cbn [until_return loc] in R;try discriminate;
 try solve [injection R as <- <-;exists 0%nat,back;repeat split;lia].
 destruct(tick (State (Running off) s c)) as [[u head]|] eqn:F;[|discriminate].
 destruct(until_return fuel tick u) as [[last tail]|] eqn:T;[|discriminate].
 injection R as <- <-;destruct (IH _ _ _ T) as [n [back [Bound [Steps Ret]]]].
 exists (S n),back;split;[lia|];split;[cbn [run];rewrite F,Steps;reflexivity|exact Ret].
Qed.
End Memory.

Definition replays e p := forall x,mem(machine p) x=WriteTrace.replay (mem e) (log p) x.
Lemma composed_memory e p origin s ws : replays e p ->
 mem(cpu_state s)=WriteTrace.replay (mem(machine p)) ws -> replays e (finish origin p (s,ws)).
Proof.
 intros P M x;cbn [finish machine log];rewrite M,replay_app;apply replay_equal,P.
Qed.
Lemma segment_memory e p origin text n q : replays e p -> segment origin text n p=Some q -> replays e q.
Proof.
 intros P;unfold segment;destruct(run _ _ _) as [[s ws]|] eqn:R;[|discriminate].
 intro H;injection H as <-;apply composed_memory;[exact P|exact (run_memory _ _ _ _ _ _ R)].
Qed.
Lemma returning_memory e p origin size fuel q : replays e p -> returning origin size fuel p=Some q -> replays e q.
Proof.
 intros P;unfold returning;destruct(until_return _ _ _) as [[s ws]|] eqn:R;[|discriminate].
 intro H;injection H as <-;apply composed_memory;[exact P|].
 destruct(returned_run _ _ _ _ _ _ R) as [n [back [_ [Run _]]]];exact (run_memory _ _ _ _ _ _ Run).
Qed.
