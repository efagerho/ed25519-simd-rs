From Coq Require Import List ZArith Lia.
From Machine Require Import execution.ScalarBytes execution.LinkedCalls memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

(* Fetch from the current data memory, so a store into the symbol changes
   the next decode. The symbol extent only bounds the instruction slice. *)
Fixpoint snapshot (m:Z->Z) a size := match size with
 | O=>[] | S n=>m a::snapshot m (a+1) n end.
Definition mapped m a (text:list Z) :=
 forall i,(i<length text)%nat -> m (a+Z.of_nat i)=nth i text 0.
Lemma snapshot_mapped text : forall m a, mapped m a text -> snapshot m a (length text)=text.
Proof.
 induction text as [|b text IH];intros m a M;[reflexivity|].
 cbn [length snapshot]. f_equal.
 - specialize (M 0%nat ltac:(cbn;lia)). now rewrite Z.add_0_r in M.
 - apply IH;intros i I;specialize (M (S i) ltac:(cbn;lia)).
   cbn [nth] in M;rewrite Nat2Z.inj_succ in M.
   replace (a+1+Z.of_nat i) with (a+Z.succ (Z.of_nat i)) by lia;exact M.
Qed.

Definition fetch o size s := ScalarBytes.fetch o (snapshot (mem(cpu_state s)) o size) s.
Inductive steps o size : state -> list store -> state -> Prop :=
 | stop s : steps o size s [] s
 | advance s mid last ws tail : fetch o size s=Some(mid,ws) ->
     steps o size mid tail last -> steps o size s (ws++tail) last.

Lemma keep_image o text allowed m ws : mapped m o text ->
 (forall x,o<=x<o+Z.of_nat(length text) -> ~allowed x) ->
 confined allowed ws -> mapped (replay m ws) o text.
Proof.
 intros M Outside Safe i I;rewrite frame with (region:=allowed) by (auto;apply Outside;lia);apply M,I.
Qed.

(* The invariant is about actual executed instructions. No writable-region
   check participates in fetch, decode or execution. *)
Section Simulation.
Variables (o:Z) (text:list Z) (inv:state->Prop) (allowed:Z->Prop).
Hypothesis separate : forall x,o<=x<o+Z.of_nat(length text) -> ~allowed x.
Hypothesis safe_step : forall s t ws,inv s -> ScalarBytes.fetch o text s=Some(t,ws) ->
 confined allowed ws /\ inv t.

Lemma next_image s t ws : mapped (mem(cpu_state s)) o text ->
 ScalarBytes.fetch o text s=Some(t,ws) -> confined allowed ws ->
 mapped (mem(cpu_state t)) o text.
Proof.
 intros M F W. assert (Run:ScalarBytes.steps o text s ws t).
 { replace ws with (ws++[]) by apply app_nil_r;eapply ScalarBytes.advance;[exact F|constructor]. }
 rewrite (steps_memory _ _ _ _ _ Run);apply keep_image with (allowed:=allowed);assumption.
Qed.

Lemma to_linked s ws t : steps o (length text) s ws t -> inv s ->
 mapped (mem(cpu_state s)) o text -> ScalarBytes.steps o text s ws t.
Proof.
 induction 1 as [s|s mid last ws tail F T IH];intros I M;[constructor|].
 unfold fetch in F;rewrite (snapshot_mapped _ _ _ M) in F.
 destruct (safe_step _ _ _ I F) as [W J].
 eapply ScalarBytes.advance;[exact F|apply IH;[exact J|eapply next_image;eauto]].
Qed.

Lemma from_linked s ws t : ScalarBytes.steps o text s ws t -> inv s ->
 mapped (mem(cpu_state s)) o text -> steps o (length text) s ws t.
Proof.
 induction 1 as [s|s mid last ws tail F T IH];intros I M;[constructor|].
 destruct (safe_step _ _ _ I F) as [W J].
 eapply advance;[unfold fetch;rewrite (snapshot_mapped _ _ _ M);exact F|
 apply IH;[exact J|eapply next_image;eauto]].
Qed.
End Simulation.

Lemma append_linked o text s xs mid : ScalarBytes.steps o text s xs mid ->
 forall ys last, ScalarBytes.steps o text mid ys last -> ScalarBytes.steps o text s (xs++ys) last.
Proof.
 induction 1;intros ys final R;[exact R|rewrite <-app_assoc;eapply ScalarBytes.advance;eauto].
Qed.

Theorem same_prefixes o text s (allowed:Z->Prop) :
 mapped (mem(cpu_state s)) o text ->
 (forall x,o<=x<o+Z.of_nat(length text) -> ~allowed x) ->
 (forall ws last,ScalarBytes.steps o text s ws last -> confined allowed ws) ->
 forall ws last, steps o (length text) s ws last <-> ScalarBytes.steps o text s ws last.
Proof.
 intros M Apart All. set (reachable:=fun t=>exists xs,ScalarBytes.steps o text s xs t).
 assert (Init:reachable s) by (exists [];constructor).
 assert (Next:forall a b writes,reachable a -> ScalarBytes.fetch o text a=Some(b,writes) ->
          confined allowed writes /\ reachable b).
 { intros a b writes [xs P] F.
   assert (One:ScalarBytes.steps o text a writes b).
   { replace writes with (writes++[]) by apply app_nil_r.
     eapply ScalarBytes.advance;[exact F|constructor]. }
   pose proof(append_linked _ _ _ _ _ P _ _ One) as R.
   split;[pose proof (All _ _ R) as W;apply Forall_app in W as [_ W];exact W|exists (xs++writes);exact R]. }
 intros ws last;split;intro R.
 - exact (to_linked _ _ _ _ Apart Next _ _ _ R Init M).
 - exact (from_linked _ _ _ _ Apart Next _ _ _ R Init M).
Qed.

(* Execute exactly n instructions. Encountering an undecodable instruction
   before n steps is an error, including after an early return. *)
Definition tick := state -> option (state*list store).
Fixpoint run (n:nat) (next:tick) s := match n with
 | O=>Some(s,[]) | S k=>match next s with
 | None=>None | Some(mid,ws)=>option_map (fun '(t,tail)=>(t,ws++tail)) (run k next mid) end end.
Lemma run_prefix n next : forall s t ws,run n next s=Some(t,ws) -> forall k,(k<=n)%nat ->
 exists mid pre tail,run k next s=Some(mid,pre) /\ ws=pre++tail.
Proof.
 induction n as [|n IH];intros s t ws F [|k] K;try lia;
 try solve [exists s,[],ws;split;reflexivity].
 cbn [run] in F;destruct (next s) as [[mid own]|] eqn:E;try discriminate.
 destruct (run n next mid) as [[last rest]|] eqn:R;try discriminate;injection F as <- <-.
 destruct (IH _ _ _ R k ltac:(lia)) as [v [pre [tail [P ->]]]].
 exists v,(own++pre),tail;split;[cbn [run];rewrite E,P;reflexivity|apply app_assoc].
Qed.

Lemma run_lift o text (allowed:Z->Prop) n : forall s t ws,
 run n (ScalarBytes.fetch o text) s=Some(t,ws) -> confined allowed ws ->
 mapped (mem(cpu_state s)) o text ->
 (forall x,o<=x<o+Z.of_nat(length text) -> ~allowed x) ->
 run n (fetch o (length text)) s=Some(t,ws).
Proof.
 induction n as [|n IH];intros s t ws F W M Const;[exact F|].
 cbn [run] in F|-*. destruct (ScalarBytes.fetch o text s) as [[mid own]|] eqn:E;try discriminate.
 destruct (run n _ mid) as [[last rest]|] eqn:R;try discriminate;injection F as <- <-.
 apply Forall_app in W as [Head Tail]. unfold fetch at 1;rewrite (snapshot_mapped _ _ _ M),E.
 rewrite (IH _ _ _ R Tail);[reflexivity| |exact Const].
 exact (next_image _ _ _ Const _ _ _ M E Head).
Qed.

Lemma run_steps n o text : forall s t ws,run n (ScalarBytes.fetch o text) s=Some(t,ws) ->
 ScalarBytes.steps o text s ws t.
Proof.
 induction n as [|n IH];intros s t ws R;cbn [run] in R.
 - injection R as <- <-;constructor.
 - destruct (ScalarBytes.fetch _ _ _) as [[mid own]|] eqn:E;try discriminate.
   destruct (run n _ mid) as [[last rest]|] eqn:T;try discriminate;injection R as <- <-.
   eapply ScalarBytes.advance;[exact E|eapply IH;exact T].
Qed.

Lemma run_append next n : forall s mid xs,run n next s=Some(mid,xs) ->
 forall k t ys,run k next mid=Some(t,ys) -> run (n+k) next s=Some(t,xs++ys).
Proof.
 induction n as [|n IH];intros s mid xs F k t ys G;cbn [run] in F.
 - injection F as <- <-;exact G.
 - destruct(next s) as [[u own]|] eqn:E;try discriminate.
   destruct(run n next u) as [[v rest]|] eqn:R;try discriminate;injection F as <- <-.
   cbn [Nat.add run];rewrite E,(IH _ _ _ R _ _ _ G);cbn [option_map];now rewrite app_assoc.
Qed.

Definition prefix_result n next s (allowed:Z->Prop) (post:state->Prop) :=
 exists t ws,run n next s=Some(t,ws) /\ post t /\
 mem(cpu_state t)=replay (mem(cpu_state s)) ws /\
 forall k,(k<=n)%nat -> exists mid pre,run k next s=Some(mid,pre) /\ confined allowed pre.

Lemma mapped_segment n o text s (allowed:Z->Prop) (post:state->Prop) :
 (exists t ws,run n (ScalarBytes.fetch o text) s=Some(t,ws) /\ confined allowed ws /\ post t) ->
 mapped (mem(cpu_state s)) o text -> (forall x,o<=x<o+Z.of_nat(length text) -> ~allowed x) ->
 prefix_result n (fetch o (length text)) s allowed post.
Proof.
 intros [t [ws [R [W End]]]] Image Apart.
 pose proof(run_lift _ _ _ _ _ _ _ R W Image Apart) as M.
 exists t,ws;split;[exact M|split;[exact End|split]].
 - exact (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R)).
 - intros k K;destruct(run_prefix _ _ _ _ _ M k K) as [mid [pre [tail [Prefix ->]]]].
   exists mid,pre;split;[exact Prefix|now apply Forall_app in W as [W _]].
Qed.
