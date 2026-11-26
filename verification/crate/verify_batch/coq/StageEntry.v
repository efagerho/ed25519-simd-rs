From Coq Require Import Bool List ZArith Lia.
From Machine Require Import execution.ScalarBytes execution.LinkedCalls execution.WordSemantics
 execution.WordBounds memory.WriteTrace memory.MemoryGeometry memory.FlatMemory memory.ByteMemory.
From Machine Require execution.LinkedRun execution.MappedFetch execution.ScalarWords.
From Ed25519Simd.VerifyBatch Require TailCopy IndexStores CallerSpills StagedRows.
From Machine Require execution.PreservedRegister execution.Cutpoint.
From Ed25519Simd.VerifyBatch Require Import Image Rows Scatter Return EntryWrites Prologue TailWrites StageWrites DescriptorStores.
Import ListNotations. Local Open Scope Z_scope.

From Ed25519Simd.VerifyBatch Require ChunkRows.
(* Run from the actual entry to the first transfer out of the wrapper image.
   The linked-image certificate below proves that preparation is that exit. *)
Definition observe ip (text:list Z) e carry :=
 let size:=length text in
 Cutpoint.until size (Cutpoint.outside size) (MappedFetch.fetch ip size) (State (Running 0) e carry).

Lemma observed_run ip text e carry t ws : observe ip text e carry=Some(t,ws) ->
 exists n,MappedFetch.run n (MappedFetch.fetch ip (length text)) (State (Running 0) e carry)=Some(t,ws).
Proof. intro H;destruct (Cutpoint.sound _ _ _ _ _ _ H) as [n [_ [R _]]];now exists n. Qed.

Definition begin o text e cf := option_map (LinkedRun.finish o (LinkedRun.initial o e cf))
 (observe o text e cf).

Lemma begin_words o text e cf p : well_formed e -> begin o text e cf=Some p -> well_formed(LinkedRun.machine p).
Proof.
 intros W;unfold begin;destruct (observe o text e cf) as [[stage ws]|] eqn:Seen;[|discriminate].
 intros [= <-];destruct (observed_run _ _ _ _ _ _ Seen) as [n Run].
 exact (ScalarWords.mapped_run_wf _ _ _ (ScalarBytes.State (ScalarBytes.Running 0) e cf) _ _ W Run).
Qed.

Definition saved_caller e s := CallerSpills.saved e (mem s) /\ regs s 5%nat=regs e 5%nat.

Definition next_descriptor e value:=(8<count e)%nat -> value=word(regs e 7%nat+320).

Definition handoff ip (text:list Z) delta e carry child :=
 StageWrites.entered ip delta e child /\
 StagedRows.original_bytes e 0 (count e) (mem(cpu_state child)) /\
 StagedRows.indices e 0 (count e) (mem(cpu_state child)) /\ saved_caller e (cpu_state child) /\
 (regs(cpu_state child) 2%nat=regs e 8%nat /\ regs(cpu_state child) 15%nat=Return.scratch e /\
   CallerSpills.table_arguments e (mem(cpu_state child))) /\ next_descriptor e (regs(cpu_state child) 3%nat) /\
 exists stage before after n k,
 loc stage=Running (offset Stage) /\
 MappedFetch.run n (MappedFetch.fetch ip (length text)) (State (Running 0) e carry)=Some(stage,before) /\
 MappedFetch.run k (MappedFetch.fetch ip (length text)) stage=Some(child,after) /\
 StageWrites.matrix (Rows.frame e) (cpu_state stage) (mem (cpu_state child)).

Definition physical ip (text:list Z) delta e := forall carry,
 Cutpoint.verified_exit ip (length text) (length text) (State (Running 0) e carry)
   (writable e) (handoff ip text delta e carry).

(* Checked on the extracted bytes for each policy. The target lies outside
   the wrapper even after relocating the relative call into a 64-bit PC. *)
Definition checked_layout (text:list Z) delta :=
 let size:=Z.of_nat(length text) in
 (offset TailDone <=? size) && (size <? 2^32) &&
 ((-2^62 <? delta) && (delta <? 2^62) && ((delta <? 0) || (size <=? delta))) &&
 PreservedRegister.checks_at 5 text 0 (length text).

(* Apply the byte certificate once. The caller supplies the semantic
   handoff, using RBP preservation if its postcondition needs it. *)
Local Lemma checked_handoff ip text delta e carry n child ws :
 checked_layout text delta=true -> (n<=Z.to_nat(offset TailDone))%nat ->
 Cutpoint.path (ScalarBytes.fetch ip text) (writable e) n (State (Running 0) e carry) child ws ->
 MappedFetch.mapped (mem e) ip text -> (forall x,ip<=x<ip+Z.of_nat(length text) -> ~writable e x) ->
 StageWrites.entered ip delta e child ->
 (regs(cpu_state child) 5%nat=regs e 5%nat -> handoff ip text delta e carry child) ->
 Cutpoint.verified_exit ip (length text) (length text) (State (Running 0) e carry)
   (writable e) (handoff ip text delta e carry).
Proof.
 intros Layout Bound [Run Writes] Image Apart ABI Post.
 unfold checked_layout in Layout;repeat rewrite Bool.andb_true_iff in Layout.
 destruct Layout as [[[Extent Len] [[Lo Hi] Ext]] Check].
 apply Z.leb_le in Extent;apply Z.ltb_lt in Len,Lo,Hi;apply Bool.orb_true_iff in Ext.
 assert (Fuel:(n<=length text)%nat) by lia.
 eapply Cutpoint.exit_checked;[exact Run|exact Writes|apply Post|exact Image|exact Apart|exact Fuel|].
 - eapply PreservedRegister.run_keeps_at;[exact Len| |exact Run].
   eapply PreservedRegister.checks_at_prefix;[exact Fuel|exact Check].
 - apply (Cutpoint.relocated_outside ip _ delta);[exact Len|exact (conj Lo Hi)| |exact (proj1 ABI)].
   destruct Ext as [E|E];[left;apply Z.ltb_lt|right;apply Z.leb_le];exact E.
Qed.

Theorem from_entry ip text delta e : Prologue.bound text -> ChunkRows.Selection.bound text -> TailWrites.bound text ->
 StageWrites.bound text delta -> checked_layout text delta=true -> placement e -> (0<count e)%nat ->
 fits64 (regs e 7%nat) (40*Z.of_nat(count e)) ->
 (forall x, regs e 7%nat<=x<regs e 7%nat+40*Z.of_nat(count e) -> ~writable e x) -> MappedFetch.mapped (mem e) ip text ->
 (forall x,ip<=x<ip+Z.of_nat(length text) -> ~Return.writable e x) -> physical ip text delta e.
Proof.
 intros Intro Select Tail Transfer RBP P N Fit RowsApart Image Apart carry.
 destruct (Prologue.execute ip text e carry Intro P N) as [[l s c] [front [F [W [End [SP [BX [Count Scratch]]]]]]]].
 cbn [loc cpu_state] in End,SP,BX,Count;subst l.
 apply Prologue.stack_writable in W.
 assert (CountZ:Z.of_nat (count e)=regs e 6%nat) by (unfold count;apply Z2Nat.id,(initial_cpu _ P)).
 assert (FirstBase:regs s 3%nat=ChunkRows.base e 0) by (unfold ChunkRows.base;rewrite BX;ring).
 destruct (Cutpoint.mapped_path (conj F W) Image Apart) as [[Front _] _].
 pose proof (ScalarWords.mapped_run_wf _ _ _ (State (Running 0) e carry) _ _ (initial_cpu _ P) Front) as Words.
 assert (Outside:preserved (fun x=>~writable e x) (mem e) (mem s)).
 { intro x.
   pose proof (steps_memory _ _ _ _ _ (MappedFetch.run_steps _ _ _ _ _ _ F)) as Replay.
   change (mem s=WriteTrace.replay (mem e) front) in Replay;rewrite Replay;apply WriteTrace.frame,W. }
 destruct (ChunkRows.choose ip text e 0 (count e) s c Select Tail P (conj Fit RowsApart) N eq_refl
   (conj SP Scratch) FirstBase (eq_trans Count (eq_sym CountZ)) (proj2(proj2 Words)) Outside)
   as [t [cf [pad [Pad [Safe Selected]]]]].
 assert (Left:Z.of_nat(count e-8)=Prologue.rows_left (regs e 6%nat)).
 { rewrite <-CountZ;unfold Prologue.rows_left.
   rewrite word_fits by (rewrite CountZ;apply (initial_cpu _ P)).
   destruct (Z.ltb_spec (Z.of_nat (count e)) 8);[lia|].
   rewrite word_fits;[lia|rewrite CountZ;pose proof (proj1(initial_cpu _ P) 6%nat);unfold word64 in *;lia]. }
 destruct (CallerSpills.from_entry ip text e carry _ _ Intro P N F) as [Saved Tables].
 destruct (StagedRows.transfer ip text delta e 0 (count e) s t cf Transfer P Selected Saved Tables)
   as [child [stores [Body [Bounds [ABI Matrix Bytes Meta Id ChildScratch Slots Table Next]]]]].
 rewrite Left in ABI.
 apply Prologue.stack_writable in Safe,Bounds.
 pose proof (Cutpoint.join (conj F W) (conj Pad Safe)) as FirstPath.
 pose proof (Cutpoint.join FirstPath (conj Body Bounds)) as Whole.
 destruct (Cutpoint.mapped_path FirstPath Image Apart) as [[ToStage _] StageImage].
 eapply checked_handoff;[exact RBP| |exact Whole|exact Image|exact Apart|exact ABI|].
 { unfold ChunkRows.length;destruct (count e <? 8)%nat;vm_compute;lia. }
 intro KeepBP.
 split;[exact ABI|split;[exact Bytes|split;[exact Meta|split;[exact (conj Slots KeepBP)|]]]].
 split;[exact (conj Id (conj ChildScratch Table))|split].
 { intro Long;rewrite (Next Long);unfold ChunkRows.base;f_equal;ring. }
 eexists (State (Running (offset Stage)) t cf),(front++pad),stores,_,_.
 split;[reflexivity|split;[exact ToStage|split;[|exact Matrix]]].
 eapply MappedFetch.run_lift;[exact Body|exact Bounds|exact StageImage|exact Apart].
Qed.

Lemma observed ip text delta e carry : physical ip text delta e ->
 exists t ws, observe ip text e carry=Some(t,ws) /\ StageWrites.entered ip delta e t /\ confined (writable e) ws.
Proof.
 intro H;destruct (H carry) as [t [ws [Run [End [Safe _]]]]].
 exists t,ws;exact (conj Run (conj (proj1 End) Safe)).
Qed.
