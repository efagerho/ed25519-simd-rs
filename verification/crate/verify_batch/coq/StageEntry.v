From Coq Require Import Bool List ZArith Lia.
From Machine Require Import isa.Instructions execution.ScalarBytes execution.LinkedCalls execution.WordSemantics
 execution.WordBounds memory.WriteTrace memory.MemoryGeometry memory.FlatMemory memory.ByteMemory.
From Machine Require execution.MappedFetch execution.ScalarWords execution.InstructionRoute.
From Ed25519Simd.VerifyBatch Require TailCopy IndexStores CallerSpills.
From Machine Require execution.PreservedRegister.
From Ed25519Simd.VerifyBatch Require Import Image Rows Scatter Return EntryWrites Prologue TailWrites StageWrites DescriptorStores.
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
Lemma pad_code text : bound text ->
 InstructionRoute.linked text TailCopy.start /\ InstructionRoute.linked text TailCopy.jump.
Proof.
 intros B;unfold bound,listing in B.
 do 12 (let D:=fresh in apply Forall_cons_iff in B as [D B];cbv beta iota in D).
 repeat constructor;try discriminate;assumption.
Qed.
Definition full_path := firstn 4 listing.
Lemma full_active ip text s c frame : bound text -> 8<=word(regs s 12%nat) ->
 regs s 4%nat=frame -> fits64 frame 960 ->
 exists t cf ws,MappedFetch.run 4 (ScalarBytes.fetch ip text) (State (Running 56) s c)=Some(State (Running 82) t cf,ws) /\
 read_word (mem t) (frame+928)=8 /\ forall x,frame+936<=x -> mem t x=mem s x.
Proof.
 intros B Full SP Fit;assert (Code:InstructionRoute.linked text full_path).
 { unfold bound,listing in B;do 4 (let H:=fresh in apply Forall_cons_iff in B as [H B];cbv beta iota in H).
   repeat constructor;try discriminate;assumption. }
 assert (FalseCmp:(word(regs s 12%nat)<?8)=false) by (apply Z.ltb_ge;lia).
 do 3 eexists;split.
 - apply (InstructionRoute.checked _ _ _ Code);cbn [full_path firstn listing InstructionRoute.follow
   loc cf cpu_state ScalarBytes.step eval_condition option_map];rewrite FalseCmp;reflexivity.
 - cbn [loc cf cpu_state ScalarBytes.step eval_condition option_map set set_regs with_zf regs with_words mem effective].
   rewrite SP,Z.add_0_r,(word_fits (frame+928)) by (destruct Fit;unfold word64;lia).
   split;[apply read_word_exact;[unfold word64;lia|intros k K;apply write_at,K]|].
   intros x X;unfold commit;cbn [qword address size payload];apply write_outside;change (~frame+928<=x<frame+928+8);lia.
Qed.
Definition active e := Z.of_nat (Nat.min (count e) 8).
Definition index_value e j := Policy.descriptor (mem e) (regs e 7%nat) (TailCopy.row_index e j) 32.
Definition metadata e := IndexStores.metadata (Rows.frame e) (active e) (index_value e).
Definition reached e st := loc st=Running (offset Stage) /\ caller_registers e (cpu_state st).

Local Ltac ins_at a :=
 match goal with D:Prologue.at_offset ?text a ?n ?op |- _=>
  eapply Prologue.more;
  [rewrite (EntryWrites.fetch_at _ text a _ _ n op ltac:(lia) D);cbn [ScalarBytes.step];reflexivity| |]
 end.
Lemma after_tail ip text e s c : bound text -> TailWrites.bound text -> placement e ->
 caller_registers e s -> Prologue.segment ip text e 88 (offset Tail) s c (fun t=>reached e t /\ regs(cpu_state t) 12%nat=0).
Proof.
 intros B Pad P SP;unfold bound,listing in B.
 do 12 (let D:=fresh "ins" in apply Forall_cons_iff in B as [D B];cbv beta iota in D).
 assert (Slot:Prologue.frame_word e (Rows.frame e+928)) by (unfold Prologue.frame_word,Rows.frame,sp;lia).
 assert (Frame:word (Rows.frame e)=Rows.frame e).
 { apply word_fits;destruct(stack_ok _ P) as [[A H] _];unfold Rows.frame,sp,word64 in *;lia. }
 ins_at 610.
 - cbn [effective];rewrite (proj1 SP),Z.add_0_r,(Prologue.slot_word _ _ P Slot);apply Prologue.slot_allowed,Slot.
 - Local Ltac keep_rsp SP :=
     lazymatch goal with |-Prologue.segment _ _ ?e _ _ ?s _ _=>
       let u:=fresh "mid" in set (u:=s);let R:=fresh "rsp" in
       assert (R:caller_registers e u) by exact SP;clearbody u;clear SP;rename R into SP
     end.
   keep_rsp SP.
   ins_at 618;[constructor|keep_rsp SP]. ins_at 621;[constructor|keep_rsp SP].
   ins_at 625;[constructor|keep_rsp SP]. ins_at 630;[constructor|].
   lazymatch goal with |-Prologue.segment _ _ _ _ _ ?s _ _=>set (u:=s) end.
   assert (BX:regs u 3%nat=Rows.frame e).
   { change (word(regs mid2 4%nat+0+0)=Rows.frame e);rewrite (proj1 SP),!Z.add_0_r;exact Frame. }
   assert (Stack:caller_registers e u) by exact SP. clearbody u.
   ins_at 634;[constructor|]. ins_at 637;[constructor|].
   lazymatch goal with |-Prologue.segment _ _ _ _ _ ?s ?carry _=>
     let V:=fresh in assert (V:TailWrites.pointers e 0 s) by (split;[exact BX|split;[reflexivity|exact (conj Stack eq_refl)]]);
     destruct (TailWrites.remaining ip text e Pad P 8 0 s carry eq_refl V)
       as [[l v cf] [ws [R [W End]]]]
   end.
   destruct End as [End [RSP Left]];cbn [loc cpu_state] in End,RSP,Left;subst l.
   assert (Jump: Prologue.segment ip text e 1 (offset TailDone) v cf (fun t=>reached e t /\ regs(cpu_state t) 12%nat=0)).
   { ins_at 679;[constructor|apply Prologue.finish;exact (conj (conj eq_refl RSP) Left)]. }
   destruct Jump as [last [tail [T [Safe Done]]]];exists last,(ws++tail).
   split;[|split;[apply Forall_app;auto|exact Done]].
   exact (MappedFetch.run_append _ 80 _ _ _ R 1 _ _ T).
Qed.

Lemma choose ip text e s c : bound text -> TailWrites.bound text -> placement e ->
 caller_registers e s -> Prologue.segment ip text e (if word (regs s 12%nat) <? 8 then 90 else 4) (offset Choose) s c (fun st=>reached e st /\
    (8<=word(regs s 12%nat) -> regs (cpu_state st) 3%nat=regs s 3%nat) /\
    regs(cpu_state st) 12%nat=Prologue.rows_left (regs s 12%nat)).
Proof.
 intros B Pad P SP. pose proof B as Ops;unfold bound,listing in Ops.
 do 4 (let D:=fresh "ins" in apply Forall_cons_iff in Ops as [D Ops];cbv beta iota in D).
 destruct (word (regs s 12%nat) <? 8) eqn:Below.
 - eapply Prologue.more;[rewrite (EntryWrites.fetch_at ip text 56 _ _ _ _ ltac:(lia) ins);
    cbn [ScalarBytes.step];rewrite Below;reflexivity|constructor|].
   ins_at 60;[constructor|].
   lazymatch goal with |-Prologue.segment _ _ _ _ _ ?s ?c _ =>
    destruct (after_tail ip text e s c B Pad P SP) as [t [ws [R [W [End Left]]]]];
    exists t,ws;split;[exact R|split;[exact W|split;[exact End|split;[apply Z.ltb_lt in Below;lia|unfold Prologue.rows_left;now rewrite Below]]]]
   end.
 - eapply Prologue.more;[rewrite (EntryWrites.fetch_at ip text 56 _ _ _ _ ltac:(lia) ins);
    cbn [ScalarBytes.step];rewrite Below;reflexivity|constructor|].
   ins_at 60;[constructor|]. ins_at 66.
   + cbn [effective with_zf regs];rewrite (proj1 SP),Z.add_0_r.
     assert (Slot:Prologue.frame_word e (Rows.frame e+928)) by (unfold Prologue.frame_word,Rows.frame,sp;lia).
     rewrite (Prologue.slot_word _ _ P Slot);apply Prologue.slot_allowed,Slot.
   + ins_at 78;[constructor|apply Prologue.finish;split;[split;[reflexivity|exact SP]|split;[reflexivity|unfold Prologue.rows_left;rewrite Below;reflexivity]]].
Qed.


(* Peek at the machine counter after register setup to select the exact
   instruction count. Both runs start from the original memory. *)
Definition budget ip (text:list Z) e carry :=
 option_map (fun '(t,_)=>if word (regs (cpu_state t) 12%nat) <? 8 then 147%nat else 61%nat)
   (MappedFetch.run 15 (MappedFetch.fetch ip (length text)) (State (Running 0) e carry)).
Definition observe ip (text:list Z) e carry :=
 match budget ip text e carry with
 | None=>None | Some n=>MappedFetch.run n (MappedFetch.fetch ip (length text)) (State (Running 0) e carry) end.
Definition saved_caller e s := CallerSpills.saved e (mem s) /\ regs s 5%nat=regs e 5%nat.

Definition handoff ip (text:list Z) delta e carry n child :=
 StageWrites.entered ip delta e child /\
 (forall j f k,(j<8)%nat -> (f<4)%nat -> 0<=k<8 ->
   mem (cpu_state child) (bank (Rows.frame e) f+8*Z.of_nat j+k)=
   mem e (regs e 7%nat+40*Z.of_nat (TailCopy.row_index e j)+8*Z.of_nat f+k)) /\ metadata e (mem(cpu_state child)) /\ saved_caller e (cpu_state child) /\
 (regs(cpu_state child) 2%nat=regs e 8%nat /\ regs(cpu_state child) 15%nat=Return.scratch e /\
   CallerSpills.table_arguments e (mem(cpu_state child))) /\ exists stage writes,
 MappedFetch.run (n-42) (MappedFetch.fetch ip (length text)) (State (Running 0) e carry)=Some(stage,writes) /\
 StageWrites.matrix (Rows.frame e) (cpu_state stage) (mem (cpu_state child)).

Definition physical ip (text:list Z) delta e := forall carry,exists n,(n=61%nat \/ n=147%nat) /\
 budget ip text e carry=Some n /\
 MappedFetch.prefix_result n (MappedFetch.fetch ip (length text)) (State (Running 0) e carry)
 (writable e) (handoff ip text delta e carry n).

Definition preserves_bp text:=(Z.of_nat(length text)<?2^32) &&
 PreservedRegister.checks_at 5 text 0 61 && PreservedRegister.checks_at 5 text 0 147.

Theorem from_entry ip text delta e : Prologue.bound text -> bound text -> TailWrites.bound text ->
 StageWrites.bound text delta -> preserves_bp text=true -> placement e -> (0<count e)%nat ->
 fits64 (regs e 7%nat) (40*Z.of_nat(count e)) ->
 (forall x, regs e 7%nat<=x<regs e 7%nat+40*Z.of_nat(count e) -> ~writable e x) -> MappedFetch.mapped (mem e) ip text ->
 (forall x,ip<=x<ip+Z.of_nat(length text) -> ~Return.writable e x) -> physical ip text delta e.
Proof.
 intros Intro Select Tail Transfer RBP P N Fit RowsApart Image Apart carry.
 destruct (Prologue.execute ip text e carry Intro P N) as [[l s c] [front [F [W [End [SP [BX [Count Scratch]]]]]]]].
 cbn [loc cpu_state] in End,SP,BX,Count;subst l.
 destruct (choose ip text e s c Select Tail P (conj SP Scratch)) as [[l t cf] [pad [Pad [Safe [[PC Frame] [Full Left]]]]]].
 cbn [loc cpu_state] in PC,Frame,Full,Left;rewrite Count in Left;subst l.
 destruct (StageWrites.instructions ip text delta e t cf Transfer P (proj1 Frame) (proj2 Frame) Left) as [child [stores [Body [Bounds [ABI [Matrix [Identity ChildScratch]]]]]]].
 set (short:=(word (regs s 12%nat) <? 8)) in *.
 set (n:=(15+(if short then 90 else 4)+42)%nat).
 exists n;split;[unfold n;destruct short;auto|].
 split.
 - unfold budget;rewrite (MappedFetch.run_lift _ _ _ _ _ _ _ F W Image Apart).
   cbn [option_map cpu_state];fold short;unfold n;destruct short;reflexivity.
 - apply (MappedFetch.mapped_segment _ _ text);[|exact Image|exact Apart].
   pose proof(MappedFetch.run_append _ _ _ _ _ F _ _ _ Pad) as First.
   exists child,((front++pad)++stores);split;[eapply MappedFetch.run_append;[exact First|exact Body]|].
   split;[unfold confined in *;rewrite !Forall_app;auto|].
   assert (CountZ: Z.of_nat (count e)=regs e 6%nat).
   { unfold count;apply Z2Nat.id;apply (initial_cpu _ P). }
   assert (FrameFit:fits64 (Rows.frame e) 960).
   { destruct(stack_ok _ P) as [[Lo Hi] _];unfold fits64,Rows.frame,sp in *;lia. }
   set (rows:=regs e 7%nat) in *;set (base:=regs t 3%nat).
   assert (Away:disjoint (Rows.frame e) 960 rows (40*regs e 6%nat)).
   { unfold disjoint;destruct (Z_le_dec (Rows.frame e+960) rows);[auto|right].
     destruct (Z_le_dec (rows+40*regs e 6%nat) (Rows.frame e));[auto|].
     exfalso;apply (RowsApart (Z.max (Rows.frame e) rows) ltac:(lia));left;unfold span,Rows.frame,sp in *;lia. }
   assert (Source:fits64 base 320 /\ IndexStores.allowed_inputs (Rows.frame e) base /\
       read_word (mem t) (Rows.frame e+928)=active e /\
       (forall x,Rows.frame e+936<=x -> mem t x=mem s x) /\ forall j k,(j<8)%nat -> 0<=k<40 -> mem t (base+40*Z.of_nat j+k)=mem e (rows+40*Z.of_nat(TailCopy.row_index e j)+k)).
   { unfold short in Pad. destruct (word (regs s 12%nat) <? 8) eqn:Small.
     - assert (Size:1<=regs e 6%nat<8).
       { apply Z.ltb_lt in Small;rewrite Count,(word_fits _ (proj1(initial_cpu _ P) _)) in Small;lia. }
       pose proof (MappedFetch.run_lift _ _ _ _ _ _ _ F W Image Apart) as Mapped.
       pose proof (ScalarWords.mapped_run_wf _ _ _ (State (Running 0) e carry) _ _ (initial_cpu _ P) Mapped) as Words.
       destruct (pad_code _ Select) as [Start Jump].
       assert (Original:forall x,rows<=x<rows+40*regs e 6%nat -> mem s x=mem e x).
       { intros x X;pose proof (steps_memory _ _ _ _ _ (MappedFetch.run_steps _ _ _ _ _ _ F)) as M.
         cbn [cpu_state] in M;rewrite M;apply (WriteTrace.frame _ _ W),RowsApart;lia. }
       rewrite CountZ in Fit.
       destruct(TailCopy.staged ip text (Rows.frame e) rows (regs e 6%nat) (mem e) s c
         Start Jump Tail Size Fit FrameFit Away SP BX Count (proj2(proj2 Words)) Original) as [v [cv [ws [Run [Base [Data [Active High]]]]]]].
       change (MappedFetch.run 90 (ScalarBytes.fetch ip text) (State (Running 56) s c)=Some(State (Running 82) t cf,pad)) in Pad.
       rewrite Pad in Run;injection Run as <- <- <-. unfold base;rewrite Base.
       split;[unfold fits64 in *;lia|split;[unfold IndexStores.allowed_inputs,disjoint;lia|]].
       split;[rewrite Active;unfold active;rewrite Nat.min_l;lia|].
       split;[exact High|]. intros j k J K;rewrite (Data j k J K);unfold rows;now rewrite TailCopy.source_row by exact N.
     - apply Z.ltb_ge in Small.
       assert (Live:(8<=count e)%nat) by (rewrite Count,(word_fits _ (proj1(initial_cpu _ P) _)) in Small;lia).
       destruct (full_active ip text s c (Rows.frame e) Select Small SP FrameFit) as [v [cv [ws [R [Active High]]]]].
       change (MappedFetch.run 4 (ScalarBytes.fetch ip text) (State (Running 56) s c)=Some(State (Running 82) t cf,pad)) in Pad.
       rewrite Pad in R;injection R as <- <- <-. unfold base;rewrite (Full Small),BX.
       split;[unfold fits64 in *;lia|split;[unfold IndexStores.allowed_inputs,disjoint in *;lia|]].
       split;[rewrite Active;unfold active;rewrite Nat.min_r by lia;reflexivity|].
       split;[exact High|]. intros j k J K;rewrite TailCopy.own_row by lia.
       pose proof(steps_memory _ _ _ _ _ (MappedFetch.run_steps _ _ _ _ _ _ First)) as M;cbn [cpu_state] in M;rewrite M.
       apply (WriteTrace.frame (writable e));[apply Forall_app;auto|apply RowsApart;lia]. }
   destruct Source as [FitBase [Dis [Active [High Data]]]].
   assert (Fields:forall j off,(j<8)%nat -> 0<=off<=32 ->
     read_word (mem t) (base+40*Z.of_nat j+off)=read_word (mem e) (rows+40*Z.of_nat(TailCopy.row_index e j)+off)).
   { intros j off J H;apply PrepareChunk.Staging.read_block;intros b B;
     rewrite <- (Z.add_assoc (base+40*Z.of_nat j)),<- (Z.add_assoc (rows+40*Z.of_nat(TailCopy.row_index e j)));
     apply Data;[exact J|change (0<=b<8) in B;lia]. }
   split;[exact ABI|]. split.
   { intros j f k J H K;rewrite Matrix by assumption;unfold value;fold base.
     rewrite word_fits by (destruct FitBase;unfold word64;lia).
     rewrite Fields,read_word_byte by (try exact J;try lia;exact (proj2(proj2(initial_cpu _ P))));reflexivity. }
   assert (Kept:metadata e (mem(cpu_state child)) /\ forall x,Rows.frame e+936<=x -> mem(cpu_state child) x=mem t x).
   { apply (IndexStores.transfer ip text delta e t cf child stores base (index_value e) (active e)).
     - exact Transfer.
     - exact P.
     - exact (conj (proj1 Frame) eq_refl).
     - exact FitBase.
     - exact Dis.
     - intros j J;split;[apply read_word_bound,(initial_cpu _ P)|exact (Fields j 32 J ltac:(lia))].
     - exact Active.
     - exact Body. }
   split;[exact (proj1 Kept)|]. split.
   { split.
     - intros x X;assert (H:Rows.frame e+936<=x) by (unfold Rows.frame,sp in *;lia).
       rewrite (proj2 Kept _ H),(High _ H);exact (proj1(CallerSpills.from_entry ip text e carry _ _ Intro P N F) x X).
     - unfold preserves_bp in RBP;apply Bool.andb_true_iff in RBP as [FirstCheck ShortBudget];
       apply Bool.andb_true_iff in FirstCheck as [Size FullBudget];apply Z.ltb_lt in Size.
       assert (K:PreservedRegister.checks_at 5 text 0 n=true) by (unfold n;destruct short;[exact ShortBudget|exact FullBudget]).
       exact (PreservedRegister.run_keeps_at 5 ip text Size n 0 e carry child ((front++pad)++stores) K
                 (MappedFetch.run_append _ _ _ _ _ First _ _ _ Body)). }
   assert (Tab:CallerSpills.table_arguments e (mem t)) by
     (eapply CallerSpills.keep_tables;[intros x X;apply High;lia|exact (proj2(CallerSpills.from_entry ip text e carry _ _ Intro P N F))]).
   split;[split;[exact (eq_trans Identity (proj1 Tab))|split;[exact ChildScratch|eapply CallerSpills.keep_tables;[intros x X;apply (proj2 Kept);lia|exact Tab]]]|].
   exists (State (Running (offset Stage)) t cf),(front++pad);split;[|exact Matrix].
   replace (n-42)%nat with (15+(if short then 90 else 4))%nat by (unfold n;destruct short;reflexivity).
   eapply MappedFetch.run_lift;[exact First|apply Forall_app;split;[exact W|exact Safe]|exact Image|exact Apart].
Qed.

Lemma observed ip text delta e carry : physical ip text delta e ->
 exists t ws, observe ip text e carry=Some(t,ws) /\ StageWrites.entered ip delta e t /\ confined (writable e) ws.
Proof.
 intro H;destruct (H carry) as [n [_ [B [t [ws [Run [End [_ Prefix]]]]]]]].
 destruct (Prefix n ltac:(lia)) as [last [all [F Safe]]];rewrite Run in F;injection F as <- <-.
 exists t,ws;unfold observe;rewrite B;split;[exact Run|exact (conj (proj1 End) Safe)].
Qed.
