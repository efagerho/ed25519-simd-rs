From Coq Require Import List ZArith Bool.
From Machine Require Import Blocks ExecutionProperties.
Import ListNotations.
Open Scope Z_scope.

(* Events are emitted from the same body and terminator used by Blocks.step.
   A push records the actual fallthrough PC; a pop records the PC read by RET. *)
Inductive event := DataOp (e : effect) | Push (a : pointer) (target : pc) | Pop (a : pointer) (target : pc).
Definition exit_events c next e last :=
 match e with
 | CallRel32 _ => match pointer_at c 4 (-8) with Some a => [Push a (At next)] | None => [] end
 | Ret => match pointer_at c 4 0 with Some a => [Pop a (rip last)] | None => [] end
 | PushRbp => match pointer_at c 4 (-8), gpr c 5%nat with
   | Some a, Int n => [Push a (SavedWord (stack_word n))] | _,_ => [] end
 | PopRbp => match pointer_at c 4 0 with
   | Some a => match return_memory c a with Some t => [Pop a t] | None => [] end
   | None => [] end
 | _ => []
 end.

Fixpoint record_path fuel p l c : option (control * list event) :=
 match rip c with
 | Caller => Some (c,[])
 | SavedWord _ => None
 | At pc => match fuel with
   | O => None
   | S n =>
     match lookup (sections p) pc with
     | Some b => match exec_body p l c (body b) with
       | Some (mid,es) => match transfer l mid (after p b) (terminator b) with
         | Some next => match record_path n p l next with
           | Some (last,tail) =>
             Some (last, map DataOp es ++ exit_events mid (after p b) (terminator b) next ++ tail)
           | None => None end
         | None => None end
       | None => None end
     | None => None end
   end
 end.

Definition data_effects := flat_map (fun e => match e with DataOp op => [op] | _ => [] end).
Definition slots := pointer -> option pc.
Definition update_slots (m : slots) e : slots :=
 match e with Push a t => fun k => if ptr_eq k a then Some t else m k | _ => m end.

(* A pop must find its recorded PC in the return memory at that instant. *)
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

Lemma transfer_events l c next e last :
 transfer l c next e = Some last ->
 let es := exit_events c next e last in
 data_effects es = [] /\ fold_left update_slots es (return_memory c) = return_memory last /\
 stack_reads (return_memory c) es.
Proof.
 destruct e; cbn [transfer exit_events]; repeat match goal with
 | |- context [match ?v with _ => _ end] => destruct v eqn:?
 end; intro H; try discriminate; inversion H; subst; cbn; intuition.
Qed.

(* This identifies the instrumented execution with the existing execution,
   including the actual return-memory contents, without assuming a trace. *)
Theorem record_path_sound fuel p l c last es :
 record_path fuel p l c = Some (last,es) ->
 path fuel p l c = Some (last,data_effects es) /\
 fold_left update_slots es (return_memory c) = return_memory last /\ stack_reads (return_memory c) es.
Proof.
 revert c last es; induction fuel as [|n IH]; intros c last es H;
 cbn [record_path] in H; cbn [path]; destruct (rip c) eqn:PC;
 try discriminate; try (inversion H; subst; repeat split; reflexivity).
 destruct (lookup (sections p) address) as [b|] eqn:B; try discriminate.
 destruct (exec_body p l c (body b)) as [[mid ops]|] eqn:Body; try discriminate.
 destruct (transfer l mid (after p b) (terminator b)) as [next|] eqn:T; try discriminate.
 destruct (record_path n p l next) as [[fin tail]|] eqn:R; try discriminate.
 inversion H; subst. destruct (IH _ _ _ R) as [P [S Reads]].
 destruct (transfer_events _ _ _ _ _ T) as [E [M Read]].
 destruct (body_writes _ _ _ _ _ _ Body) as [_ Same].
 unfold dispatch,block_control; rewrite PC,B,Body,T,P.
 unfold data_effects in E |- *; rewrite !flat_map_app; fold data_effects in *.
 rewrite data_events,E. cbn [app]. rewrite !reads_app, !fold_left_app, data_slots, <-Same, M.
 intuition auto using reads_data.
Qed.

(* Each live entry pairs the address of its stack slot with its expected PC.
   A CALL must use a free slot; a RET must consume the most recent entry. *)
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
