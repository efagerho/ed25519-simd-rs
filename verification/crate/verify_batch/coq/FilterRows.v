From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 memory.ByteMemory memory.FlatMemory memory.MemoryGeometry.
From Curve25519.group Require Import Decompression PrimeField.
From Ed25519Simd.DalekPostHash Require Keys Caller.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require FilterPass Tables.
Local Open Scope Z_scope.

Definition slot e x:=StrictFilterCall.slot e-16<=x<StrictFilterCall.slot e-8.
Definition ptr e s j:=read_word (mem s) (PrepareOutputs.dest e+8*Z.of_nat j).
Definition view e s:=with_words s (put (regs s) 6 (PrepareOutputs.dest e)) (mem s).
Definition rows e s:=forall j,(j<8)%nat -> let a:=ptr e s j in
 fits64 a 2720 /\ forall x,a<=x<a+2720 -> ~slot e x.

Lemma readable bias outer e prep p : placement e -> loaded Dalek bias (mem e) (writable e) -> Tables.mapped e bias ->
 PreparedReturn.result Dalek bias outer e prep -> StrictFilterCall.entry bias e prep p -> rows e (machine p).
Proof.
 intros P I [_ [Id _]] Done E j J.
 assert (Ptr:ptr e (machine p) j=ptr e (machine prep) j).
 { unfold ptr;apply preserved_read with (outside:=fun x=>~span (StrictFilterCall.slot e) 8 x).
   - intros x N;rewrite (StrictFilterCall.memory_after _ _ _ _ E);apply write_outside,N.
   - intros k K;change (0<=k<8) in K;unfold span,StrictFilterCall.slot,common_top,PrepareOutputs.dest;lia. }
 rewrite Ptr;destruct(PreparedReturn.selected _ _ _ _ _ Done j J) as [Local Original].
 assert (Dec:RootDecision.decodes false e j \/ ~RootDecision.decodes false e j).
 { unfold RootDecision.decodes;set (y:=residue (BatchDecode.original_encoding false e j mod 2^255)).
   pose proof(decode_correct y false) as H;destruct (decode y false) as [x|];[left;exists x;apply H|right;intros [x X];exact (H x X)]. }
 destruct Dec as [D|D].
 - change (RootDecision.decodes false e j -> ptr e (machine prep) j=scratch e+PrepareChunk.Caller.table_offset j) in Local.
   rewrite (Local D);destruct(scratch_ok _ P) as [[L H] _];pose proof(scratch_stack _ P);
   unfold PrepareChunk.Caller.table_offset,PrepareChunk.Caller.tables_offset,PrepareChunk.Caller.table_stride,slot,StrictFilterCall.slot,common_top,Rows.frame,sp,disjoint,fits64 in *;intuition lia.
 - change (~RootDecision.decodes false e j -> ptr e (machine prep) j=regs e 8%nat) in Original.
   rewrite (Original D),Id;assert (Addr:In (IdentityTable.address,2720) static_tables) by (right;left;reflexivity).
   split;[apply (tables_fit _ _ _ _ I _ _ Addr)|intros x X S;apply (immutable _ _ _ _ I x);[right;exists IdentityTable.address,2720;auto|]].
   left;unfold span,slot,StrictFilterCall.slot,common_top,Rows.frame,sp in *;lia.
Qed.

Definition addresses e s t:=forall j,(j<8)%nat -> vectors t j 20%nat=ptr e s j.
Lemma cell e s t j c i : rows e s -> addresses e s t -> preserved (fun x=>~slot e x) (mem s) (mem t) ->
 (j<8)%nat -> 0<=c<4 -> (i<5)%nat ->
 FilterColumns.cell t j c i=DalekPostHash.Keys.column (view e s) j c i.
Proof.
 intros Rows Addr M J C N;destruct(Rows j J) as [[Lo Hi] Out].
 unfold FilterColumns.cell;rewrite Addr by exact J;unfold DalekPostHash.Keys.column.
 change (read_word (mem t) (word(ptr e s j+DalekPostHash.Caller.table_disp c i))=
         read_word (mem s) (ptr e s j+DalekPostHash.Caller.table_disp c i)).
 rewrite word_fits by (unfold word64,DalekPostHash.Caller.table_disp;lia).
 apply preserved_read with (outside:=fun x=>~slot e x);[exact M|intros k K;change (0<=k<8) in K;apply Out;unfold DalekPostHash.Caller.table_disp;lia].
Qed.
Lemma bias_word s j i : FilterCarry.constants s -> (i<5)%nat -> vectors s j (FilterColumns.bias_reg i)=DalekPostHash.Keys.bias i.
Proof.
 intros C N;unfold FilterColumns.bias_reg,DalekPostHash.Keys.bias;destruct (Nat.eqb i 0);
 [exact (C 2%nat j ltac:(lia))|exact (C 3%nat j ltac:(lia))].
Qed.

Lemma first e s t j : rows e s -> addresses e s t -> preserved (fun x=>~slot e x) (mem s) (mem t) ->
 FilterCarry.constants t -> (j<8)%nat -> FilterPass.matched false t j=DalekPostHash.Keys.first (view e s) j.
Proof.
 intros R A M C J;apply FilterPass.same_test;intros i N.
 change (FilterColumns.minus_plus t j i=DalekPostHash.Keys.biased false
    (DalekPostHash.Keys.column (view e s) j 1) (DalekPostHash.Keys.column (view e s) j 0) i).
 unfold FilterColumns.minus_plus,DalekPostHash.Keys.biased;rewrite !cell with (e:=e) (s:=s) by (assumption || lia);now rewrite bias_word.
Qed.
Lemma second e s t j : rows e s -> addresses e s t -> preserved (fun x=>~slot e x) (mem s) (mem t) ->
 FilterCarry.constants t -> (forall i,(i<5)%nat -> vectors t j (15+i)%nat=DalekPostHash.Keys.column (view e s) j 0 i) ->
 (j<8)%nat -> FilterPass.matched true t j=DalekPostHash.Keys.second (view e s) j.
Proof.
 intros R A M C Lo J;apply FilterPass.same_test;intros i N.
 change (FilterColumns.twice_minus_z t j i=DalekPostHash.Keys.biased true
    (DalekPostHash.Keys.column (view e s) j 0) (DalekPostHash.Keys.column (view e s) j 3) i).
 unfold FilterColumns.twice_minus_z,DalekPostHash.Keys.biased;rewrite Lo,bias_word,(cell e s) by (assumption || lia);reflexivity.
Qed.
