From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.ScalarBytes execution.LinkedCalls execution.WordSemantics
 execution.WordBounds memory.WriteTrace.
From Machine Require execution.MappedFetch.
From Ed25519Simd.VerifyBatch Require Import Image Rows Scatter Return EntryWrites Prologue TailWrites StageWrites.
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
Definition reached e st := loc st=Running (offset Stage) /\ regs (cpu_state st) 4%nat=Rows.frame e.

Local Ltac ins_at a :=
 match goal with D:Prologue.at_offset ?text a ?n ?op |- _=>
  eapply Prologue.more;
  [rewrite (EntryWrites.fetch_at _ text a _ _ n op ltac:(lia) D);cbn [ScalarBytes.step];reflexivity| |]
 end.
Lemma after_tail ip text e s c : bound text -> TailWrites.bound text -> placement e ->
 regs s 4%nat=Rows.frame e -> Prologue.segment ip text e 88 (offset Tail) s c (reached e).
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
   assert (Stack:regs u 4%nat=Rows.frame e) by exact SP. clearbody u.
   ins_at 634;[constructor|]. ins_at 637;[constructor|].
   lazymatch goal with |-Prologue.segment _ _ _ _ _ ?s ?carry _=>
     let V:=fresh in assert (V:TailWrites.pointers e 0 s) by (repeat split;[exact BX|exact Stack]);
     destruct (TailWrites.remaining ip text e Pad P 8 0 s carry eq_refl V)
       as [[l v cf] [ws [R [W End]]]]
   end.
   destruct End as [End RSP];cbn [loc cpu_state] in End,RSP;subst l.
   assert (Jump: Prologue.segment ip text e 1 (offset TailDone) v cf (reached e)).
   { ins_at 679;[constructor|apply Prologue.finish;split;[reflexivity|exact RSP]]. }
   destruct Jump as [last [tail [T [Safe Done]]]];exists last,(ws++tail).
   split;[|split;[apply Forall_app;auto|exact Done]].
   exact (MappedFetch.run_append _ 80 _ _ _ R 1 _ _ T).
Qed.

Lemma choose ip text e s c : bound text -> TailWrites.bound text -> placement e ->
 regs s 4%nat=Rows.frame e -> Prologue.segment ip text e (if word (regs s 12%nat) <? 8 then 90 else 4) (offset Choose) s c (reached e).
Proof.
 intros B Pad P SP. pose proof B as Ops;unfold bound,listing in Ops.
 do 4 (let D:=fresh "ins" in apply Forall_cons_iff in Ops as [D Ops];cbv beta iota in D).
 destruct (word (regs s 12%nat) <? 8) eqn:Below.
 - eapply Prologue.more;[rewrite (EntryWrites.fetch_at ip text 56 _ _ _ _ ltac:(lia) ins);
    cbn [ScalarBytes.step];rewrite Below;reflexivity|constructor|].
   ins_at 60;[constructor|]. apply after_tail;assumption.
 - eapply Prologue.more;[rewrite (EntryWrites.fetch_at ip text 56 _ _ _ _ ltac:(lia) ins);
    cbn [ScalarBytes.step];rewrite Below;reflexivity|constructor|].
   ins_at 60;[constructor|]. ins_at 66.
   + cbn [effective with_zf regs];rewrite SP,Z.add_0_r.
     assert (Slot:Prologue.frame_word e (Rows.frame e+928)) by (unfold Prologue.frame_word,Rows.frame,sp;lia).
     rewrite (Prologue.slot_word _ _ P Slot);apply Prologue.slot_allowed,Slot.
   + ins_at 78;[constructor|apply Prologue.finish;split;[reflexivity|exact SP]].
Qed.


(* Peek at the machine counter after register setup to select the exact
   instruction count. Both runs start from the original memory. *)
Definition budget ip (text:list Z) e carry :=
 option_map (fun '(t,_)=>if word (regs (cpu_state t) 12%nat) <? 8 then 147%nat else 61%nat)
   (MappedFetch.run 15 (MappedFetch.fetch ip (length text)) (State (Running 0) e carry)).
Definition observe ip (text:list Z) e carry :=
 match budget ip text e carry with
 | None=>None | Some n=>MappedFetch.run n (MappedFetch.fetch ip (length text)) (State (Running 0) e carry) end.
Definition physical ip (text:list Z) delta e := forall carry,exists n,(n=61%nat \/ n=147%nat) /\
 budget ip text e carry=Some n /\
 MappedFetch.prefix_result n (MappedFetch.fetch ip (length text)) (State (Running 0) e carry)
 (writable e) (StageWrites.entered ip delta e).

Theorem from_entry ip text delta e : Prologue.bound text -> bound text -> TailWrites.bound text ->
 StageWrites.bound text delta -> placement e -> (0<count e)%nat -> MappedFetch.mapped (mem e) ip text ->
 (forall x,ip<=x<ip+Z.of_nat(length text) -> ~Return.writable e x) -> physical ip text delta e.
Proof.
 intros Intro Select Tail Transfer P N Image Apart carry.
 destruct (Prologue.execute ip text e carry Intro P N) as [[l s c] [front [F [W [End SP]]]]].
 cbn [loc cpu_state] in End,SP;subst l.
 destruct (choose ip text e s c Select Tail P SP) as [[l t cf] [pad [Pad [Safe [PC Frame]]]]].
 cbn [loc cpu_state] in PC,Frame;subst l.
 destruct (StageWrites.instructions ip text delta e t cf Transfer P Frame) as [child [stores [Body [Bounds ABI]]]].
 set (short:=(word (regs s 12%nat) <? 8)) in *.
 set (n:=(15+(if short then 90 else 4)+42)%nat).
 exists n;split;[unfold n;destruct short;auto|].
 split.
 - unfold budget;rewrite (MappedFetch.run_lift _ _ _ _ _ _ _ F W Image Apart).
   cbn [option_map cpu_state];fold short;unfold n;destruct short;reflexivity.
 - apply (MappedFetch.mapped_segment _ _ text);[|exact Image|exact Apart].
   pose proof(MappedFetch.run_append _ _ _ _ _ F _ _ _ Pad) as First.
   exists child,((front++pad)++stores);split;[eapply MappedFetch.run_append;[exact First|exact Body]|].
   split;[unfold confined in *;rewrite !Forall_app;auto|exact ABI].
Qed.

Lemma observed ip text delta e carry : physical ip text delta e ->
 exists t ws, observe ip text e carry=Some(t,ws) /\ StageWrites.entered ip delta e t /\ confined (writable e) ws.
Proof.
 intro H;destruct (H carry) as [n [_ [B [t [ws [Run [End [_ Prefix]]]]]]]].
 destruct (Prefix n ltac:(lia)) as [last [all [F Safe]]];rewrite Run in F;injection F as <- <-.
 exists t,ws;unfold observe;now rewrite B.
Qed.
