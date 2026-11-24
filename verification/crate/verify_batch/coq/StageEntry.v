From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.ScalarBytes execution.LinkedCalls execution.WordSemantics
 execution.WordBounds memory.WriteTrace.
From Machine Require execution.MappedFetch.
From Ed25519Simd.VerifyBatch Require Import Image Rows Scatter Return EntryWrites Prologue TailWrites.
Import ListNotations. Local Open Scope Z_scope.

Definition listing : list (Z*nat*ScalarBytes.instruction) :=
 [(56,4%nat,CompareImm 12 8);(60,6%nat,Branch ScalarBytes.Below (offset Tail-66));
  (66,12%nat,StoreImmediate (Address 4 None 928) 8);(78,4%nat,Sub64 12 8);
  (610,8%nat,Store64 12 (Address 4 None 928));(618,3%nat,CopyG 6 3);
  (621,4%nat,LeaG 0 (Address 12 (Some (12%nat,4)) 0));
  (625,5%nat,LeaG 7 (Address 3 (Some (0%nat,8)) (-40)));
  (630,4%nat,LeaG 3 (Address 4 None 0));(634,3%nat,Zero32 12);(637,2%nat,Zero32 1);
  (679,5%nat,ScalarBytes.Jump (offset Stage-684))].
Definition bound text := Forall (fun '(a,n,i)=>Prologue.at_offset text a n i) listing.
Definition reached st := loc st=Running (offset Stage).

Local Ltac ins_at a :=
 match goal with D:Prologue.at_offset ?text a ?n ?op |- _=>
  eapply Prologue.more;
  [rewrite (EntryWrites.fetch_at _ text a _ _ n op ltac:(lia) D);cbn [ScalarBytes.step];reflexivity| |]
 end.
Lemma after_tail ip text e s c : bound text -> TailWrites.bound text -> placement e ->
 regs s 4%nat=Rows.frame e -> Prologue.segment ip text e 88 (offset Tail) s c reached.
Proof.
 intros B Pad P SP;unfold bound,listing in B.
 do 12 (let D:=fresh "ins" in apply Forall_cons_iff in B as [D B];cbv beta iota in D).
 assert (Slot:Prologue.frame_word e (Rows.frame e+928)) by (unfold Prologue.frame_word,Rows.frame,sp;lia).
 assert (Frame:word (Rows.frame e)=Rows.frame e).
 { apply word_fits;destruct(stack_ok _ P) as [[A H] _];unfold Rows.frame,sp,word64 in *;lia. }
 ins_at 610.
 - cbn [effective];rewrite SP,Z.add_0_r,(Prologue.slot_word _ _ P Slot);apply Prologue.slot_allowed,Slot.
 - Local Ltac keep_rsp SP :=
     lazymatch goal with |-Prologue.segment _ _ ?e _ _ ?s _ _=>
       let u:=fresh "mid" in set (u:=s);let R:=fresh "rsp" in
       assert (R:regs u 4%nat=Rows.frame e) by exact SP;clearbody u;clear SP;rename R into SP
     end.
   keep_rsp SP.
   ins_at 618;[constructor|keep_rsp SP]. ins_at 621;[constructor|keep_rsp SP].
   ins_at 625;[constructor|keep_rsp SP]. ins_at 630;[constructor|].
   lazymatch goal with |-Prologue.segment _ _ _ _ _ ?s _ _=>set (u:=s) end.
   assert (BX:regs u 3%nat=Rows.frame e).
   { change (word(regs mid2 4%nat+0+0)=Rows.frame e);rewrite SP,!Z.add_0_r;exact Frame. }
   clearbody u.
   ins_at 634;[constructor|]. ins_at 637;[constructor|].
   lazymatch goal with |-Prologue.segment _ _ _ _ _ ?s ?carry _=>
     let V:=fresh in assert (V:TailWrites.pointers e 0 s) by (split;[exact BX|reflexivity]);
     destruct (TailWrites.remaining ip text e Pad P 8 0 s carry eq_refl V)
       as [[l v cf] [ws [R [W End]]]]
   end.
   unfold TailWrites.reached in End;cbn [loc] in End;subst l.
   assert (Jump: Prologue.segment ip text e 1 (offset TailDone) v cf reached).
   { ins_at 679;[constructor|apply Prologue.finish;reflexivity]. }
   destruct Jump as [last [tail [T [Safe Done]]]];exists last,(ws++tail).
   split;[|split;[apply Forall_app;auto|exact Done]].
   exact (MappedFetch.run_append _ 80 _ _ _ R 1 _ _ T).
Qed.

Lemma choose ip text e s c : bound text -> TailWrites.bound text -> placement e ->
 regs s 4%nat=Rows.frame e -> exists n, (n=4%nat \/ n=90%nat) /\
 Prologue.segment ip text e n (offset Choose) s c reached.
Proof.
 intros B Pad P SP. pose proof B as Ops;unfold bound,listing in Ops.
 do 4 (let D:=fresh "ins" in apply Forall_cons_iff in Ops as [D Ops];cbv beta iota in D).
 destruct (word (regs s 12%nat) <? 8) eqn:Below.
 - exists 90%nat;split;[auto|].
   eapply Prologue.more;[rewrite (EntryWrites.fetch_at ip text 56 _ _ _ _ ltac:(lia) ins);
    cbn [ScalarBytes.step];rewrite Below;reflexivity|constructor|].
   ins_at 60;[constructor|]. apply after_tail;assumption.
 - exists 4%nat;split;[auto|].
   eapply Prologue.more;[rewrite (EntryWrites.fetch_at ip text 56 _ _ _ _ ltac:(lia) ins);
    cbn [ScalarBytes.step];rewrite Below;reflexivity|constructor|].
   ins_at 60;[constructor|]. ins_at 66.
   + cbn [effective with_zf regs];rewrite SP,Z.add_0_r.
     assert (Slot:Prologue.frame_word e (Rows.frame e+928)) by (unfold Prologue.frame_word,Rows.frame,sp;lia).
     rewrite (Prologue.slot_word _ _ P Slot);apply Prologue.slot_allowed,Slot.
   + ins_at 78;[constructor|apply Prologue.finish;reflexivity].
Qed.

Definition physical ip (text:list Z) e := forall carry,exists n,(n=19%nat \/ n=105%nat) /\
 MappedFetch.prefix_result n (MappedFetch.fetch ip (length text)) (State (Running 0) e carry)
 (writable e) reached.
Theorem from_entry ip text e : Prologue.bound text -> bound text -> TailWrites.bound text ->
 placement e -> (0<count e)%nat -> MappedFetch.mapped (mem e) ip text ->
 (forall x,ip<=x<ip+Z.of_nat(length text) -> ~Return.writable e x) -> physical ip text e.
Proof.
 intros Intro Body Tail P N Image Apart carry.
 destruct (Prologue.execute ip text e carry Intro P N) as [[l s c] [front [F [W [End SP]]]]].
 cbn [loc cpu_state] in End,SP;subst l.
 destruct (choose ip text e s c Body Tail P SP) as [n [Len [t [back [R [Safe Done]]]]]].
 exists (15+n)%nat;split;[lia|apply (MappedFetch.mapped_segment _ _ text);[|exact Image|exact Apart]].
 exists t,(front++back);split;[eapply MappedFetch.run_append;[exact F|exact R]|].
 split;[apply Forall_app;auto|exact Done].
Qed.

(* Choose the first of the two possible arrivals at the transpose by looking
   at RIP in the execution. Neither branch inspects the event addresses. *)
Definition arrives t := match loc t with Running a=>a=?offset Stage | Returned _=>false end.
Lemma arrival t : reached t -> arrives t=true.
Proof. intro R;unfold reached in R;unfold arrives;rewrite R;apply Z.eqb_refl. Qed.
Definition observe ip (text:list Z) e carry :=
 let start:=State (Running 0) e carry in let next:=MappedFetch.fetch ip (length text) in
 match MappedFetch.run 19 next start with
 | Some(t,ws)=>if arrives t then Some(t,ws) else MappedFetch.run 105 next start
 | None=>None end.
Lemma observed ip text e carry : physical ip text e ->
 exists t ws, observe ip text e carry=Some(t,ws) /\ reached t /\ confined (writable e) ws.
Proof.
 intro H;destruct (H carry) as [n [N [t [ws [R [End [Replay Prefix]]]]]]].
 destruct (Prefix n ltac:(lia)) as [last [all [F Safe]]];rewrite R in F;injection F as <- <-.
 unfold observe;destruct N as [->| ->].
 - rewrite R,(arrival _ End);eauto.
 - destruct (Prefix 19%nat ltac:(lia)) as [mid [pre [P W]]];rewrite P;destruct (arrives mid) eqn:A.
   + exists mid,pre;split;[reflexivity|split;[|exact W]].
     unfold arrives in A;unfold reached;destruct (loc mid);[apply Z.eqb_eq in A;now subst|discriminate].
   + exists t,ws;split;[exact R|split;assumption].
Qed.
