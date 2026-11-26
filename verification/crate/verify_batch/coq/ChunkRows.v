From Coq Require Import Bool List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds execution.WordSemantics
 execution.ScalarBytes execution.MappedFetch memory.ByteMemory memory.FlatMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Rows Return Image EntryWrites Prologue TailWrites.
From Machine Require isa.Instructions.
From Machine Require execution.InstructionRoute.
From Ed25519Simd.PrepareChunk Require Staging.
From Ed25519Simd.VerifyBatch Require TailCopy IndexStores.
Import ListNotations.
Local Open Scope Z_scope.
Module Selection.
Import Instructions.
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
End Selection.

Definition base e first:=regs e 7%nat+40*Z.of_nat first.
Definition lane first n j:=(first+Nat.min j (n-1))%nat.
Definition active n:=Z.of_nat(Nat.min n 8).
Definition length n:=if (n<?8)%nat then 90%nat else 4%nat.
Definition readable e:=fits64 (regs e 7%nat) (40*Z.of_nat(Scatter.count e)) /\
 forall x,regs e 7%nat<=x<regs e 7%nat+40*Z.of_nat(Scatter.count e) -> ~writable e x.
Definition words e first n s:=forall j k,(j<8)%nat -> 0<=k<40 ->
 mem s (regs s 3%nat+40*Z.of_nat j+k)=mem e (base e (lane first n j)+k).
Definition allowed e first n := fits64 (base e first) (40*Z.of_nat n) /\
 disjoint (Rows.frame e) 960 (base e first) (40*Z.of_nat n).
Lemma bounds e first n:readable e -> (0<n)%nat -> (first+n<=Scatter.count e)%nat -> allowed e first n.
Proof.
 intros [[L H] Sep] Live N;unfold allowed,base;split;[unfold fits64 in *;lia|unfold disjoint].
 destruct (Z_le_dec (Rows.frame e+960) (regs e 7%nat+40*Z.of_nat first));[auto|right].
 destruct (Z_le_dec (regs e 7%nat+40*Z.of_nat first+40*Z.of_nat n) (Rows.frame e));[auto|].
 exfalso;set(x:=Z.max (Rows.frame e) (regs e 7%nat+40*Z.of_nat first));apply (Sep x ltac:(unfold x;lia));left;unfold x,Rows.frame,sp,span in *;lia.
Qed.

Record selected e first n s t:Prop:=Selected {
 stack:TailWrites.caller_registers e t; left:regs t 12%nat=Z.of_nat(n-8);
 row_area:fits64 (regs t 3%nat) 320 /\ IndexStores.allowed_inputs (Rows.frame e) (regs t 3%nat);
 count_slot:read_word (mem t) (Rows.frame e+928)=active n;
 above:forall x,Rows.frame e+936<=x -> mem t x=mem s x;
 bytes:words e first n t;
 next_base:(8<=n)%nat -> regs t 3%nat=base e first
}.

Theorem choose ip text e first n s c:Selection.bound text -> TailWrites.bound text -> placement e ->
 readable e -> (0<n)%nat -> (first+n=Scatter.count e)%nat ->
 TailWrites.caller_registers e s -> regs s 3%nat=base e first -> regs s 12%nat=Z.of_nat n ->
 byte_memory(mem s) -> preserved (fun x=>~writable e x) (mem e) (mem s) ->
 exists t cf ws,run (length n) (ScalarBytes.fetch ip text) (State(Running(Image.offset Image.Choose)) s c)=
  Some(State(Running(Image.offset Image.Stage)) t cf,ws) /\ confined (Prologue.stack_region e) ws /\ selected e first n s t.
Proof.
 intros Select Tail P Read N Total Frame BX Count Bytes Outside;pose proof(bounds e first n Read N ltac:(lia)) as [Fit Away].
 destruct(Read) as [_ Sep];destruct(stack_ok _ P) as [[Low High] _].
 assert (FF:fits64 (Rows.frame e) 960) by (unfold fits64,Rows.frame,sp in *;lia).
 assert (W:word(regs s 12%nat)=Z.of_nat n) by (rewrite Count;apply word_fits;pose proof(proj1(initial_cpu _ P) 6%nat);unfold Scatter.count,word64 in *;lia).
 assert (Original:forall x,base e first<=x<base e first+40*Z.of_nat n -> mem s x=mem e x) by (intros x X;apply Outside,Sep;unfold base in *;lia).
 destruct(Selection.choose ip text e s c Select Tail P Frame) as [[l t cf] [ws [Run [Safe [[PC St] [Full Rem]]]]]].
 cbn [loc cpu_state] in PC,St,Full,Rem;subst l;rewrite W in Run,Full.
 assert (Left:regs t 12%nat=Z.of_nat(n-8)).
 { rewrite Rem;unfold Prologue.rows_left;rewrite W;destruct(Z.ltb_spec (Z.of_nat n) 8);[lia|].
   rewrite word_fits;[lia|pose proof(proj1(initial_cpu _ P) 6%nat);unfold Scatter.count,word64 in *;lia]. }
 assert (AlignedCount: (Z.of_nat n<?8)=(n<?8)%nat) by (destruct(Z.ltb_spec (Z.of_nat n) 8), (Nat.ltb_spec n 8);auto;lia).
 rewrite AlignedCount in Run;exists t,cf,ws;split;[exact Run|split;[exact Safe|]].
 destruct (Nat.ltb_spec n 8) as [Short|Long].
 - destruct(Selection.pad_code _ Select) as [Start Jump];destruct(TailCopy.staged ip text (Rows.frame e) (base e first) (Z.of_nat n)
     (mem e) s c Start Jump Tail ltac:(lia) Fit FF Away (proj1 Frame) BX Count Bytes Original) as [u [cf' [writes [TailRun [Base [Data [Active HighMem]]]]]]].
   change (run 90 (ScalarBytes.fetch ip text) (State(Running 56) s c)=Some(State(Running 82) t cf,ws)) in Run.
   rewrite Run in TailRun;injection TailRun as <- <- <-;constructor;[exact St|exact Left| | |exact HighMem| |lia].
   + rewrite Base;split;[unfold fits64 in *;lia|unfold IndexStores.allowed_inputs,disjoint;lia].
   + rewrite Active;unfold active;rewrite Nat.min_l by lia;reflexivity.
   + intros j k J K;rewrite Base,Data by assumption;unfold TailCopy.source,base,lane.
     rewrite Nat2Z.inj_add,Nat2Z.inj_min,Nat2Z.inj_sub by lia;change (Z.of_nat 1) with 1;apply f_equal;ring.
 - assert (Base:regs t 3%nat=base e first) by (rewrite Full by lia;exact BX).
   destruct(Selection.full_active ip text s c (Rows.frame e) Select ltac:(rewrite W;lia) (proj1 Frame) FF)
      as [u [cu [w [Raw [Active HighMem]]]]].
   change (run 4 (ScalarBytes.fetch ip text) (State(Running 56) s c)=Some(State(Running 82) t cf,ws)) in Run.
   rewrite Run in Raw;injection Raw as <- <- <-.
   constructor;[exact St|exact Left| | |exact HighMem| |auto].
   + rewrite Base;split;[unfold fits64 in *;lia|unfold IndexStores.allowed_inputs,disjoint in *;lia].
   + rewrite Active;unfold active;rewrite Nat.min_r by lia;reflexivity.
   + intros j k J K;rewrite Base;unfold lane;rewrite Nat.min_l by lia;unfold base;rewrite Nat2Z.inj_add.
     pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Run)) as M;cbn [cpu_state] in M;rewrite M;
     apply Prologue.stack_writable in Safe;rewrite (WriteTrace.frame _ _ Safe),Outside;[f_equal;ring|apply Sep;lia|apply Sep;lia].
Qed.


Lemma selected_word e first n s t : selected e first n s t ->
 forall j off,(j<8)%nat -> 0<=off<=32 ->
 read_word (mem t) (regs t 3%nat+40*Z.of_nat j+off)=
 read_word (mem e) (base e (lane first n j)+off).
Proof.
 intros Selected j off J K;apply PrepareChunk.Staging.read_block;intros k B.
 rewrite <-(Z.add_assoc (regs t 3%nat+40*Z.of_nat j) off k),<-(Z.add_assoc (base e (lane first n j)) off k).
 apply (bytes _ _ _ _ _ Selected j);[exact J|change (0<=k<8) in B;lia].
Qed.
