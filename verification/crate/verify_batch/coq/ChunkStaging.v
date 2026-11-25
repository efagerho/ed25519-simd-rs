From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds execution.WordSemantics execution.ScalarBytes
 execution.MappedFetch execution.ScalarWords memory.ByteMemory memory.FlatMemory memory.MemoryGeometry memory.WriteTrace.
From Machine Require execution.PreservedRegister.
From Ed25519Simd.PrepareChunk Require Staging.
From Ed25519Simd.VerifyBatch Require Import Policy Rows Image Return TailWrites StageEntry.
From Ed25519Simd.VerifyBatch Require ChunkRows StageCursor.
Local Open Scope Z_scope.
Definition index e first n j:=descriptor (mem e) (regs e 7%nat) (ChunkRows.lane first n j) 32.
Definition execute o text n:=segment o text (ChunkRows.length n+42).
Record entry o delta e first n q:Prop:=Entry {
 target:ip q=word(o+delta); paid:accounted e (writable e) q; valid:well_formed(machine q);
 stack:regs(machine q) 4%nat=Rows.frame e-8; return_slot:read_word(mem(machine q))(Rows.frame e-8)=word(o+offset Prepared);
 matrix:forall j f k,(j<8)%nat -> (f<4)%nat -> 0<=k<8 ->
   mem(machine q)(DescriptorStores.bank (Rows.frame e) f+8*Z.of_nat j+k)=
   mem e (ChunkRows.base e (ChunkRows.lane first n j)+8*Z.of_nat f+k);
 metadata:IndexStores.metadata (Rows.frame e) (ChunkRows.active n) (index e first n) (mem(machine q));
 arguments:regs(machine q) 6%nat=Rows.frame e+512 /\ regs(machine q) 1%nat=Rows.frame e+768 /\
   regs(machine q) 7%nat=scratch e /\ regs(machine q) 2%nat=regs e 8%nat;
 globals:Prologue.context_registers e (machine q);
 remaining:regs(machine q) 12%nat=Z.of_nat(n-8);
 descriptor_cursor:(8<n)%nat -> regs(machine q) 3%nat=ChunkRows.base e (first+8);
 saved:StageEntry.saved_caller e (machine q); tables:CallerSpills.table_arguments e (mem(machine q))
}.

Definition preserves_bp text := (Z.of_nat(List.length text)<?2^32) &&
 PreservedRegister.checks_at 5 text 56 46 && PreservedRegister.checks_at 5 text 56 132.
Theorem checked_frame o text delta e first n p : StageEntry.bound text -> TailWrites.bound text -> StageWrites.bound text delta ->
 preserves_bp text=true -> placement e -> ChunkRows.readable e -> (0<n)%nat -> (first+n=Scatter.count e)%nat ->
 mapped (mem e) o text -> (forall x,o<=x<o+Z.of_nat(List.length text) -> ~writable e x) ->
 ip p=o+offset Choose -> accounted e (writable e) p -> well_formed(machine p) ->
 caller_registers e (machine p) -> regs(machine p) 3%nat=ChunkRows.base e first -> regs(machine p) 12%nat=Z.of_nat n ->
 StageEntry.saved_caller e (machine p) -> CallerSpills.table_arguments e (mem(machine p)) ->
 exists q,execute o text n p=Some q /\ entry o delta e first n q /\
 preserved (Return.span (output e) (Z.of_nat(Scatter.count e))) (mem(machine p)) (mem(machine q)).
Proof.
 intros Choose Tail Transfer BP P Read Live N Map Sep PC Paid W Caller BX Count [Saved OldBP] Tables.
 set(s:=machine p) in *;set(f:=Rows.frame e).
 assert (Outside:preserved (fun x=>~writable e x) (mem e) (mem s)) by (intros x X;rewrite (proj2 Paid);apply (WriteTrace.frame _ _ (proj1 Paid)),X).
 destruct(ChunkRows.choose o text e first n s (LinkedRun.carry p) Choose Tail P Read Live N Caller BX Count (proj2(proj2 W)) Outside)
   as [t [cf [ws [Select [Safe S]]]]].
 destruct(ChunkRows.stack _ _ _ _ _ S) as [SP Glob].
 destruct(StageWrites.instructions_with o text delta e (Z.of_nat(n-8)) t cf Transfer P SP Glob (ChunkRows.left _ _ _ _ _ S))
   as [v [w [Body [Writes [[Dest [Top [Ret [SI [CX [DI [Out Left]]]]]]] [Matrix [Table Scratch]]]]]]].
 pose proof(run_append _ _ _ _ _ Select _ _ _ Body) as Total;assert(Conf:confined (writable e)(ws++w)) by (apply Prologue.stack_writable,Forall_app;auto).
 destruct(at_segment _ _ _ o text _ _ _ _ Paid PC (image_after _ _ _ _ _ Paid Map Sep) Sep Total Conf) as [Run Done].
 set(q:=LinkedRun.finish o p (v,ws++w)) in *.
 assert (Rows:forall j off,(j<8)%nat -> 0<=off<=32 ->
   read_word (mem t) (regs t 3%nat+40*Z.of_nat j+off)=read_word(mem e) (ChunkRows.base e (ChunkRows.lane first n j)+off)).
 { intros j off J K;apply PrepareChunk.Staging.read_block;intros i I;rewrite <-(Z.add_assoc (regs t 3%nat+40*Z.of_nat j) off i),<-(Z.add_assoc (ChunkRows.base e (ChunkRows.lane first n j)) off i);apply (ChunkRows.bytes _ _ _ _ _ S j);[exact J|change (0<=i<8) in I;lia]. }
 destruct(ChunkRows.row_area _ _ _ _ _ S) as [Fits Away].
 destruct(IndexStores.transfer o text delta e t cf v w (regs t 3%nat) (index e first n) (ChunkRows.active n)
     Transfer P (conj SP eq_refl) Fits Away ltac:(intros j J;split;[apply read_word_bound,(initial_cpu _ P)|apply (Rows j 32 J);lia])
     (ChunkRows.count_slot _ _ _ _ _ S) Body) as [Indices Upper].
 assert (High:forall x,f+936<=x -> mem(cpu_state v) x=mem s x).
 { intros x X;rewrite Upper by exact X;exact(ChunkRows.above _ _ _ _ _ S x X). }
 assert (Pointer:regs(cpu_state v) 3%nat=word(regs t 3%nat+320)) by exact(proj1(StageCursor.advanced _ _ _ _ _ _ _ _ Transfer P SP Body)).
 exists q;split;[exact Run|split].
 2:{ intros x X;change (mem(cpu_state v) x=mem s x).
     rewrite (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Total)).
     apply (WriteTrace.frame (Prologue.stack_region e));[apply Forall_app;auto|].
     destruct(out_stack _ P);unfold Prologue.stack_region,span,disjoint in *;lia. }
 constructor.
 - change (absolute o v=word(o+delta));unfold absolute;rewrite Dest;ring.
 - exact Done.
 - exact (segment_wf _ _ _ _ _ W Run).
 - exact Top.
 - exact Ret.
 - intros j g k J G K;change (mem(cpu_state v)(DescriptorStores.bank (Rows.frame e) g+8*Z.of_nat j+k)=mem e (ChunkRows.base e (ChunkRows.lane first n j)+8*Z.of_nat g+k));rewrite Matrix by assumption;unfold DescriptorStores.value;
   rewrite word_fits by (unfold fits64,word64 in *;lia);rewrite (Rows j (8*Z.of_nat g) J ltac:(lia)).
   apply read_word_byte;[apply(initial_cpu _ P)|exact K].
 - exact Indices.
 - split;[exact SI|split;[exact CX|split;[exact DI|]]];change (regs(cpu_state v) 2%nat=regs e 8%nat);rewrite Table;apply eq_trans with (read_word(mem s)(Rows.frame e+936));[|exact(proj1 Tables)].
   apply preserved_read with (outside:=fun x=>f+936<=x);[exact(ChunkRows.above _ _ _ _ _ S)|intros i I;change (0<=i<8) in I;unfold f;lia].
 - exact(conj Scratch Out).
 - exact Left.
 - intro More;change (regs(cpu_state v) 3%nat=ChunkRows.base e (first+8));rewrite Pointer,(ChunkRows.next_base _ _ _ _ _ S) by lia;unfold ChunkRows.base;rewrite Nat2Z.inj_add.
   destruct Read as [[Lo Hi] _];unfold fits64,word64 in *;rewrite word_fits by (unfold word64;lia);ring.
 - split;[intros x X;change (mem(cpu_state v) x=Return.saved_memory e x);rewrite High;[apply Saved,X|unfold f,Rows.frame,sp in *;lia]|].
   apply Bool.andb_true_iff in BP as [B Short];apply Bool.andb_true_iff in B as [Size Full];apply Z.ltb_lt in Size.
   assert (B:PreservedRegister.checks_at 5 text 56 (ChunkRows.length n+42)=true) by (unfold ChunkRows.length;destruct (n<?8)%nat;[exact Short|exact Full]).
   exact(eq_trans (PreservedRegister.run_keeps_at 5 o text Size _ _ s (LinkedRun.carry p) v _ B Total) OldBP).
 - eapply CallerSpills.keep_tables;[intros x X;apply High;lia|exact Tables].
Qed.
