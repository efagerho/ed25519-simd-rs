From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.ScalarBytes execution.WordBounds execution.WordSemantics
 memory.ByteMemory memory.FlatMemory memory.MemoryGeometry.
From Ed25519Simd.VerifyBatch Require Import Policy Image Rows Return.
From Ed25519Simd.VerifyBatch Require ChunkRows StageWrites StageCursor IndexStores CallerSpills.
Local Open Scope Z_scope.

Definition index e first n j := descriptor (mem e) (regs e 7%nat) (ChunkRows.lane first n j) 32.
Definition indices e first n := IndexStores.metadata (Rows.frame e) (ChunkRows.active n) (index e first n).
Definition original_bytes e first n m := forall j f k,(j<8)%nat -> (f<4)%nat -> 0<=k<8 ->
 m (DescriptorStores.bank (Rows.frame e) f+8*Z.of_nat j+k)=
 mem e (ChunkRows.base e (ChunkRows.lane first n j)+8*Z.of_nat f+k).

Record result origin delta e first n selected child : Prop := Result {
 entered : StageWrites.entered_with origin delta e (Z.of_nat(n-8)) child;
 matrix : StageWrites.matrix (Rows.frame e) selected (mem(cpu_state child));
 bytes : original_bytes e first n (mem(cpu_state child));
 metadata : indices e first n (mem(cpu_state child));
 table_pointer : regs(cpu_state child) 2%nat=regs e 8%nat;
 scratch_pointer : regs(cpu_state child) 15%nat=Return.scratch e;
 saved : CallerSpills.saved e (mem(cpu_state child));
 tables : CallerSpills.table_arguments e (mem(cpu_state child));
 next_descriptor : (8<n)%nat -> regs(cpu_state child) 3%nat=word(ChunkRows.base e first+320)
}.

(* At the Stage label full windows use the descriptor array and short windows
   use the padded copy. Selection already identifies the original row in both. *)
Theorem transfer origin text delta e first n before selected cf :
 StageWrites.bound text delta -> placement e -> ChunkRows.selected e first n before selected ->
 CallerSpills.saved e (mem before) -> CallerSpills.table_arguments e (mem before) ->
 Prologue.segment origin text e 42 (offset Stage) selected cf (result origin delta e first n selected).
Proof.
 intros Code P Rows Saved Tables.
 destruct (ChunkRows.stack _ _ _ _ _ Rows) as [SP Context].
 destruct (StageWrites.instructions_with origin text delta e (Z.of_nat(n-8)) selected cf Code P SP Context
   (ChunkRows.left _ _ _ _ _ Rows)) as [child [stores [Run [Safe [ABI [Matrix [Pointer Scratch]]]]]]].
 pose proof (ChunkRows.selected_word _ _ _ _ _ Rows) as Fields.
 destruct (ChunkRows.row_area _ _ _ _ _ Rows) as [Fits Away].
 destruct (IndexStores.transfer origin text delta e selected cf child stores (regs selected 3%nat)
   (index e first n) (ChunkRows.active n) Code P (conj SP eq_refl) Fits Away
   ltac:(intros j J;split;[apply read_word_bound,(initial_cpu _ P)|apply (Fields j 32 J);lia])
   (ChunkRows.count_slot _ _ _ _ _ Rows) Run) as [Metadata High].
 pose proof (ChunkRows.above _ _ _ _ _ Rows) as Above.
 assert (Tab:CallerSpills.table_arguments e (mem selected)) by
   (eapply CallerSpills.keep_tables;[intros x X;apply Above;lia|exact Tables]).
 exists child,stores;split;[exact Run|split;[exact Safe|]].
 constructor;[exact ABI|exact Matrix| |exact Metadata|exact (eq_trans Pointer (proj1 Tab))|exact Scratch| | |].
 - intros j f k J F K;rewrite Matrix by assumption;unfold DescriptorStores.value.
   rewrite word_fits by (unfold fits64,word64 in *;lia).
   rewrite (Fields j (8*Z.of_nat f) J ltac:(lia));apply read_word_byte;[apply(initial_cpu _ P)|exact K].
 - intros x X;assert (H:Rows.frame e+936<=x) by (unfold Rows.frame,sp in *;lia).
   rewrite (High _ H),(Above _ H);apply Saved,X.
 - eapply CallerSpills.keep_tables;[intros x X;apply High;lia|exact Tab].
 - intro More;rewrite (proj1(StageCursor.advanced _ _ _ _ _ _ _ _ Code P SP Run)).
   now rewrite (ChunkRows.next_base _ _ _ _ _ Rows) by lia.
Qed.
