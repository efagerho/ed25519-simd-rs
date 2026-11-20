From Coq Require Import List ZArith Bool.
From Machine Require Import execution.Blocks execution.ExecutionProperties.
Import ListNotations.
Open Scope Z_scope.

(* The recorder uses the same transfer result as ordinary execution. *)
Definition dispatch_recorded p l c : option (control * list event) :=
 match rip c with
 | Caller | SavedWord _ => None
 | At pc => match lookup (sections p) pc with
   | Some b => match exec_body p l c (body b) with
     | Some (mid,es) => match transfer_recorded l mid (after p b) (terminator b) with
       | Some (next,ts) => Some (next, map DataOp es ++ ts)
       | None => None end
     | None => None end
   | None => None end end.
Definition record_path fuel p l c := walk (dispatch_recorded p l) fuel c.
Definition slots := pointer -> option pc.

Fixpoint stack_reads (m : slots) es : Prop :=
 match es with
 | [] => True
 | e::rest => (match e with Pop a t => m a = Some t | _ => True end) /\
              stack_reads (update_slots m e) rest
 end.

Lemma data_events xs : data_effects (map DataOp xs) = xs.
Proof. induction xs; cbn; congruence. Qed.
Lemma data_slots xs (m : slots) : fold_left update_slots (map DataOp xs) m = m.
Proof. induction xs; cbn; auto. Qed.
Lemma reads_data xs m : stack_reads m (map DataOp xs).
Proof. induction xs; cbn; auto. Qed.
Lemma reads_app a b m :
 stack_reads m (a++b) <-> stack_reads m a /\ stack_reads (fold_left update_slots a m) b.
Proof. revert m; induction a; intro m; cbn; [tauto|rewrite IHa; tauto]. Qed.

Lemma transfer_events l c next e last es :
 transfer_recorded l c next e = Some (last,es) ->
 data_effects es = [] /\ fold_left update_slots es (return_memory c) = return_memory last /\
 stack_reads (return_memory c) es.
Proof.
 destruct e; cbn [transfer_recorded]; repeat match goal with
 | |- context [match ?v with _ => _ end] => destruct v eqn:?
 end; intro H; try discriminate; inversion H; subst; cbn; intuition.
Qed.

Lemma data_effects_app a b : data_effects (a++b) = data_effects a ++ data_effects b.
Proof. apply flat_map_app. Qed.
Lemma dispatch_projection p l c : dispatch p l c =
 option_map (fun '(last,es) => (last,data_effects es)) (dispatch_recorded p l c).
Proof.
 unfold dispatch, dispatch_recorded; destruct (rip c); try reflexivity.
 destruct (lookup (sections p) address) as [b|]; [|reflexivity].
 unfold block_control; destruct (exec_body p l c (body b)) as [[mid ops]|]; [|reflexivity].
 unfold transfer; destruct (transfer_recorded l mid (after p b) (terminator b)) as [[last es]|] eqn:T;
 cbn; [|reflexivity].
 destruct (transfer_events _ _ _ _ _ _ T) as [E _].
 rewrite data_effects_app, data_events, E, app_nil_r; reflexivity.
Qed.

(* State and event projections share one traversal; stack effects remain
   related to memory contents at every pop. *)
Theorem record_path_sound fuel p l c last es :
 record_path fuel p l c = Some (last,es) ->
 path fuel p l c = Some (last,data_effects es) /\
 fold_left update_slots es (return_memory c) = return_memory last /\ stack_reads (return_memory c) es.
Proof.
 intro R; split.
 - unfold path; rewrite (walk_project _ _ _ (dispatch_projection p l)).
   change (option_map (fun '(last,es) => (last,data_effects es)) (record_path fuel p l c) = Some (last,data_effects es)).
   now rewrite R.
 - revert c last es R; induction fuel as [|n IH]; intros c last es H;
   cbn [record_path walk] in H; destruct (rip c) eqn:PC; try discriminate;
   try (inversion H; subst; split; [reflexivity|exact Logic.I]).
   unfold dispatch_recorded at 1 in H; rewrite PC in H.
   destruct (lookup (sections p) address) as [b|]; [|discriminate].
   destruct (exec_body p l c (body b)) as [[mid ops]|] eqn:B; [|discriminate].
   destruct (transfer_recorded l mid (after p b) (terminator b)) as [[next ts]|] eqn:T; [|discriminate].
   destruct (walk (dispatch_recorded p l) n next) as [[fin tail]|] eqn:P; [|discriminate].
   inversion H; subst; clear H.
   destruct (body_writes _ _ _ _ _ _ B) as [_ Slots].
   destruct (transfer_events _ _ _ _ _ _ T) as [_ [Writes Reads]].
   destruct (IH _ _ _ P) as [Final Tail].
   split.
   + rewrite !fold_left_app, data_slots, <-Slots, Writes;exact Final.
   + rewrite !reads_app, !fold_left_app, !data_slots, <-Slots, Writes.
     repeat split; auto using reads_data.
Qed.

Inductive balanced : list (pointer * pc) -> list event -> Prop :=
| balanced_end : balanced [] []
| balanced_data live e rest : balanced live rest ->
    balanced live (DataOp e :: rest)
| balanced_push live a t rest : ~ In a (map fst live) ->
    balanced ((a,t)::live) rest -> balanced live (Push a t :: rest)
| balanced_pop live a t rest : balanced live rest ->
    balanced ((a,t)::live) (Pop a t :: rest).

Definition pc_eq (a b : pc) := match a,b with
 | Caller,Caller => true | At x, At y | SavedWord x, SavedWord y => x =? y | _,_ => false end.
Fixpoint check_stack (live : list (pointer * pc)) es :=
 match es with
 | [] => match live with [] => true | _ => false end
 | DataOp _ :: rest => check_stack live rest
 | Push a t :: rest => negb (existsb (ptr_eq a) (map fst live)) &&
                        check_stack ((a,t)::live) rest
 | Pop a t :: rest => match live with
   | (b,u)::tail => ptr_eq a b && pc_eq t u && check_stack tail rest
   | [] => false end
 end.
Lemma check_stack_sound es live :
 check_stack live es = true -> balanced live es.
Proof.
 revert live; induction es as [|e es IH]; intros live H; cbn in H.
 - destruct live; [constructor|discriminate].
 - destruct e as [e|a t|a t].
   + constructor; auto.
   + apply andb_true_iff in H as [U T]. constructor; [|now apply IH].
     apply negb_true_iff in U. intro I.
     assert (existsb (ptr_eq a) (map fst live) = true).
     { apply existsb_exists. exists a; split; auto. destruct a; unfold ptr_eq; cbn.
       now rewrite Nat.eqb_refl,Z.eqb_refl. } congruence.
   + destruct live as [|[b u] tail]; [discriminate|].
     repeat rewrite andb_true_iff in H. destruct H as [[A B] T].
     apply ptr_eq_true in A; subst. assert (t=u).
     { destruct t,u; cbn in B; try discriminate; try reflexivity; apply Z.eqb_eq in B; congruence. }
     subst. constructor. now apply IH.
Qed.

Lemma balanced_pop_location live es a t :
 balanced live es -> In (Pop a t) es ->
 In a (map fst live) \/ exists target, In (Push a target) es.
Proof.
 intro B; induction B as [|live e rest B IH|live slot pc rest Free B IH|live slot pc rest B IH];
   cbn; intros I.
 - contradiction.
 - destruct I as [Hit|I]; [discriminate|]. destruct (IH I) as [L|[u P]]; eauto.
 - destruct I as [Hit|I]; [discriminate|]. destruct (IH I) as [[<-|L]|[u P]]; eauto.
 - destruct I as [Hit|I]; [inversion Hit; subst; auto|]. destruct (IH I) as [L|[u P]]; eauto.
Qed.

(* Explicit loads inside a vector fragment are included in the read footprint. *)
Definition read_addresses p e := match e with
 | Read _ a=>[a]
 | Evaluate id bases=>flat_map(fun bd=>
   match find(fun entry=>Nat.eqb(fst entry)(fst bd))bases with
   | Some(_,a)=>[offset a(snd bd)] | None=>[] end)(load_operands(fragment_code p id))
 | _=>[] end.
