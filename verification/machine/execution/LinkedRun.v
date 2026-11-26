From Coq Require Import List ZArith Lia.
From Machine Require Import execution.WordSemantics execution.LinkedCalls execution.ScalarBytes
 execution.MappedFetch memory.WriteTrace.
From Machine Require execution.Composition execution.Cutpoint.
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

Lemma ensures_bind {A B : Type} (step : option A) (next : A -> option B) (middle:A->Prop) (post:B->Prop):
 Composition.ensures (Composition.output step) middle ->
 (forall a,middle a -> Composition.ensures (Composition.output (next a)) post) ->
 Composition.ensures (Composition.output (bind step next)) post.
Proof.
 intros [[a R] All] Continue. specialize (All a R). unfold Composition.output in R. rewrite R. exact (Continue a All).
Qed.

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

(* The suffix is both the extension to the incoming log and the memory
   update between these two particular instruction boundaries. *)
Definition extends_log region p q:=exists ws,log q=log p++ws /\ confined region ws /\
 forall x,mem(machine q) x=replay (mem(machine p)) ws x.

Lemma account_history e region p q : accounted e region p -> extends_log region p q -> accounted e region q.
Proof.
 intros Paid [ws [L [W M]]];destruct q as [pc s c logs];cbn [log machine] in L,M;subst logs;
 apply append_accounted;[exact Paid|exact W|exact M].
Qed.

(* The PC may be an in-symbol offset, a relative call target outside the
   symbol, or the absolute address popped by RET. *)
Lemma segment_history region o text n p off t ws : ip p=o+off -> mapped (mem(machine p)) o text ->
 (forall x,o<=x<o+Z.of_nat(length text) -> ~region x) ->
 run n (ScalarBytes.fetch o text) (ScalarBytes.State (ScalarBytes.Running off) (machine p) (carry p))=Some(t,ws) ->
 confined region ws -> let q:=finish o p (t,ws) in
 segment o text n p=Some q /\ extends_log region p q.
Proof.
 intros PC Code Sep R Safe q;split.
 - unfold segment;rewrite PC;replace (o+off-o) with off by ring;now rewrite (run_lift _ _ _ _ _ _ _ R Safe Code Sep).
 - exists ws;split;[reflexivity|split;[exact Safe|intro x;exact (f_equal (fun m=>m x) (ScalarBytes.steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R)))]].
Qed.

Lemma at_segment e allowed p origin text n off s ws : accounted e allowed p ->
 ip p=origin+off -> MappedFetch.mapped (mem (machine p)) origin text ->
 (forall x,origin<=x<origin+Z.of_nat(length text)->~allowed x) ->
 run n (ScalarBytes.fetch origin text) (State (Running off) (machine p) (carry p))=Some(s,ws) ->
 confined allowed ws ->
 segment origin text n p=Some(finish origin p (s,ws)) /\ accounted e allowed (finish origin p (s,ws)).
Proof.
 intros Prev At M Apart R Safe.
 destruct (segment_history _ _ _ _ _ _ _ _ At M Apart R Safe) as [Step History].
 exact (conj Step (account_history _ _ _ _ Prev History)).
Qed.
Lemma image_after e allowed p origin text : accounted e allowed p -> mapped (mem e) origin text ->
 (forall x,origin<=x<origin+Z.of_nat(length text)->~allowed x) -> mapped (mem(machine p)) origin text.
Proof. intros [W M] Code Sep i I;rewrite M;exact (keep_image _ _ _ _ _ Code Sep W i I). Qed.

(* Stop on the first RET. A step at a running PC that cannot be decoded
   still fails. The fuel counts instructions, including RET itself. *)
Definition at_return s := match loc s with Returned _=>true | Running _=>false end.
Definition until_return fuel := Cutpoint.until fuel at_return.

Lemma until_exact origin size k : forall fuel s t ws back, (k<=fuel)%nat ->
 run k (MappedFetch.fetch origin size) s=Some(t,ws) -> loc t=Returned back ->
 until_return fuel (MappedFetch.fetch origin size) s=Some(t,ws).
Proof.
 intros fuel s t ws back B R Ret. assert (Stopped:forall u,at_return u=true -> MappedFetch.fetch origin size u=None).
 { intros [[off|ip] cpu c];[discriminate|reflexivity]. }
 eapply (Cutpoint.terminal_exact at_return _ Stopped k);[exact B|exact R|unfold at_return;now rewrite Ret].
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
 intros s t ws R;destruct (Cutpoint.sound _ _ _ _ _ _ R) as [n [B [Run End]]].
 unfold at_return in End;destruct (loc t) as [off|back] eqn:At;[discriminate|].
 exists n,back;auto.
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
