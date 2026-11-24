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
