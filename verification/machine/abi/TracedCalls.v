From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordSemantics execution.StoreInstructions memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

Definition completed_call := Z -> cpu -> Z -> cpu -> list store -> Prop.
Definition partial_call := Z -> cpu -> list store -> Prop.

(* The call push is a caller instruction. A child receives its resulting memory
   and must return to the encoded continuation before execution resumes. *)
Fixpoint complete (call:completed_call) slide pc code s exit_ip out ws : Prop :=
 match code with []=>False | op::tail=>
 let next:=next_pc pc op in let '(ip,mid):=caller_step slide pc op s in
 let own:=caller_stores slide pc op s in
 match op with
 | Invoke _=>exists back child rest, call ip mid (word (slide+next)) back child /\
     complete call slide next tail back exit_ip out rest /\ ws=own++child++rest
 | Return=>exit_ip=ip /\ out=mid /\ ws=own
 | _=>exists rest, complete call slide next tail mid exit_ip out rest /\ ws=own++rest
 end end.

(* A prefix can stop before an instruction, within a child that has not
   returned, or in the continuation of an already completed child. *)
Fixpoint prefix (call:completed_call) (partial:partial_call) slide pc code s ws : Prop :=
 ws=[] \/ match code with []=>False | op::tail=>
 let next:=next_pc pc op in let '(ip,mid):=caller_step slide pc op s in
 let own:=caller_stores slide pc op s in
 ws=own \/ match op with
 | Invoke _=>(exists child, partial ip mid child /\ ws=own++child) \/
    exists back child rest, call ip mid (word (slide+next)) back child /\
       prefix call partial slide next tail back rest /\ ws=own++child++rest
 | Return=>False
 | _=>exists rest, prefix call partial slide next tail mid rest /\ ws=own++rest
 end end.

Lemma erasure call slide code : forall pc s ip out,
 LinkedCalls.runs (fun a e r f=>exists ws,call a e r f ws) slide pc code s ip out <->
 exists ws,complete call slide pc code s ip out ws.
Proof.
 induction code as [|op tail IH];intros pc s ip out;cbn [runs complete];[firstorder|].
 destruct (caller_step _ _ _ _) as [dest mid]. destruct op;cbn zeta;
 try solve [rewrite IH;split;[intros [rest R];eexists;exists rest;split;[exact R|reflexivity]|
    intros [ws [rest [R E]]];exists rest;exact R]].
 - split.
   + intros [back [[child C] R]]. apply IH in R as [rest R]. eexists;exists back,child,rest;split;[exact C|split;[exact R|reflexivity]].
   + intros [ws [back [child [rest [C [R _]]]]]]. exists back;split;[eauto|apply IH;eauto].
 - split;[intros [-> ->];exists [];repeat split;reflexivity|intros [ws [A [B _]]];split;assumption].
Qed.

Lemma complete_memory call
 (Child:forall a e r f ws,call a e r f ws -> mem f=WriteTrace.replay (mem e) ws)
 slide code : forall pc s ip out ws,complete call slide pc code s ip out ws ->
 mem out=WriteTrace.replay (mem s) ws.
Proof.
 induction code as [|op tail IH];intros pc s ip out ws Run;[contradiction|].
 cbn [complete] in Run. pose proof(caller_store_memory slide pc op s) as M.
 destruct (caller_step _ _ _ _) as [dest mid];cbn [snd] in M.
 destruct op;cbn zeta in Run;
 try solve [destruct Run as [rest [R ->]];rewrite replay_app,<-M;eapply IH;exact R].
 - destruct Run as [back [child [rest [C [R ->]]]]].
   rewrite !replay_app,<-M,<-(Child _ _ _ _ _ C);eapply IH;exact R.
 - destruct Run as [_ [-> ->]];exact M.
Qed.

Definition includes (parent child:Z->Prop) := forall x,child x -> parent x.
Lemma lend parent child ws : includes parent child -> confined child ws -> confined parent ws.
Proof. intros I H;unfold confined in *;rewrite Forall_forall in *;intros w W x X;apply I,(H w W),X. Qed.

(* Each call site proves containment of exactly its child's private stack
   and borrowed buffers. The caller may protect arbitrary live locations. *)
Definition private_frame (low sp:Z) (borrowed:Z->Prop) x :=
 low<=x<sp \/ borrowed x.
Lemma protects_return low sp borrowed :
 (forall x, sp<=x<sp+8 -> ~borrowed x) ->
 forall x, sp<=x<sp+8 -> ~private_frame low sp borrowed x.
Proof. unfold private_frame;intros B x X [S|S];[lia|exact (B x X S)]. Qed.

Section Composition.
Variable call : completed_call.
Variable partial : partial_call.
Variable child_region : Z -> cpu -> Z -> Prop.
Hypothesis child_prefix : forall a e ws, partial a e ws -> confined (child_region a e) ws.
Hypothesis child_return : forall a e r f ws, call a e r f ws -> confined (child_region a e) ws.

Fixpoint obligations (region:Z->Prop) slide pc code s : Prop :=
 match code with []=>True | op::tail=>
 let next:=next_pc pc op in let '(ip,mid):=caller_step slide pc op s in
 confined region (caller_stores slide pc op s) /\
 match op with
 | Invoke _=>includes region (child_region ip mid) /\
     forall back child,call ip mid (word (slide+next)) back child ->
       obligations region slide next tail back
 | Return=>True
 | _=>obligations region slide next tail mid
 end end.

Theorem composed_prefix region slide code : forall pc s ws,
 obligations region slide pc code s -> prefix call partial slide pc code s ws -> confined region ws.
Proof.
 induction code as [|op tail IH];intros pc s ws O P.
 - destruct P as [->|[]];constructor.
 - destruct P as [->|P];[constructor|]. cbn [obligations] in O.
   destruct (caller_step _ _ _ _) as [ip mid]. destruct O as [Own Continue].
   destruct P as [->|P];[exact Own|]. destruct op;cbn zeta in *;
   try solve [destruct P as [rest [R ->]];apply Forall_app;split;[exact Own|eapply IH;eauto]].
   + destruct Continue as [L Next]. destruct P as [[child [C ->]]|[back [child [rest [C [R ->]]]]]].
     * apply Forall_app;split;[exact Own|eapply lend;[exact L|eapply child_prefix;eauto]].
     * apply Forall_app;split;[exact Own|]. apply Forall_app;split.
       -- eapply lend;[exact L|eapply child_return;eauto].
       -- eapply IH;[eapply Next;eauto|exact R].
   + contradiction.
Qed.

Lemma completed_prefix slide code : forall pc s ip out ws,
 complete call slide pc code s ip out ws -> prefix call partial slide pc code s ws.
Proof.
 induction code as [|op tail IH];intros pc s ip out ws R;[contradiction|].
 right;cbn [complete] in R. destruct (caller_step _ _ _ _) as [dest mid]. destruct op;
 try solve [right; destruct R as [rest [R ->]];exists rest;split;[eapply IH;eauto|reflexivity]].
 - right;right;destruct R as [back [child [rest [C [R ->]]]]].
   exists back,child,rest;split;[exact C|split;[eapply IH;eauto|reflexivity]].
 - left;tauto.
Qed.
End Composition.

(* A store below the child's current RSP is not necessarily within the
   bottom of the reserved stack. Charge alignment loss and the CALL push
   against one ancestor's lower bound. *)
Lemma aligned_child_stack parent_sp budget current locals align child_depth :
 0<align -> 0<=locals -> 0<=child_depth -> current<=parent_sp ->
 parent_sp-current + (align-1) + locals + 8 + child_depth <= budget ->
 let call_sp := current-current mod align-locals in
 parent_sp-budget <= call_sp-8-child_depth /\ call_sp<=parent_sp.
Proof. intros A L D C B;pose proof (Z.mod_pos_bound current align A);lia. Qed.

Lemma call_push_confined slide pc dest s region :
 (forall x, word (regs s 4%nat-8)<=x<word (regs s 4%nat-8)+8 -> region x) ->
 confined region (caller_stores slide pc (Invoke dest) s).
Proof. intros P;constructor;[exact P|constructor]. Qed.
