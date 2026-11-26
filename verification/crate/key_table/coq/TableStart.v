From Coq Require Import List ZArith Lia.
From Machine Require Import abi.RegisterSpill execution.WordSemantics execution.LinkedCalls execution.LinkedRun execution.ScalarWords
 execution.VectorProcedure memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.KeyTable Require Image.
From Ed25519Simd.KeyTable Require TableIdentity TableMultiple TableProduct.
From Ed25519Simd.KeyTable Require Import CallLayout.
From Ed25519Simd.KeyTable Require NativeEntry.
Local Open Scope Z_scope.

Definition execute bias:procedure:=then_run (TableIdentity.fill bias) (TableMultiple.start bias).
Record result (root:cpu) bias e p q:Prop:=Result {
 positioned:exists c,TableMultiple.positioned root bias e 1 c q;
 point_after:preserved (span (CallLayout.point_ptr e) 1280) (mem(machine p)) (mem(machine q));
 rows:forall j i,(j<8)%nat -> 0<=i<20 ->
  read_word (mem(machine q)) (TableIdentity.center (TableIdentity.first e) j+8*i)=Image.identity_word i;
 parent:preserved (CallLayout.keep e) (Frame.saved (sp e) p) (mem(machine q))
}.

Theorem checked (root:cpu) bias e p b : placement e -> loaded root bias e ->
 NativeEntry.entered root (writable e) (CallLayout.base bias) (sp e) (point_ptr e) (table_ptr e) p b -> exists q,execute bias b=Some q /\ result root bias e p q.
Proof.
 intros P I B.
 destruct(TableIdentity.checked _ _ _ _ _ P I B) as [c [Identity C]].
 destruct(TableMultiple.first _ _ _ _ _ _ P I B C) as [d [First D]].
 assert (Input:preserved (span (CallLayout.point_ptr e) 1280) (mem(machine p)) (mem(machine d))).
 { rewrite (TableMultiple.flat _ _ _ _ _ _ D).
   intros x X;rewrite (TableIdentity.surrounding _ _ _ _ _ C).
     2:{ intros [r [R Hit]];pose proof (buffers_disjoint _ P);unfold TableIdentity.center,TableIdentity.first,disjoint,span in *;lia. }
     rewrite (NativeEntry.memory_after _ _ _ _ _ _ _ _ B);apply outside_spill.
     change (Z.of_nat(length Frame.saved_regs)) with 6;pose proof(CallLayout.point_stack _ P);
       unfold disjoint,span in *;lia. }
 exists d;split;[unfold execute,then_run;rewrite Identity;exact First|constructor].
 - now exists c.
 - exact Input.
 - intros j i J N;rewrite (TableMultiple.flat _ _ _ _ _ _ D);exact (TableIdentity.finished_rows _ _ _ _ _ C j i J N).
 - intros x K;rewrite (TableMultiple.flat _ _ _ _ _ _ D),(TableIdentity.surrounding _ _ _ _ _ C).
   + now rewrite (NativeEntry.memory_after _ _ _ _ _ _ _ _ B).
   + exact (TableIdentity.outside_keep _ _ K).
Qed.
