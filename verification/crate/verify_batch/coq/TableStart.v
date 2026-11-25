From Ed25519Simd.VerifyBatch Require TableParentFrame.
From Coq Require Import List ZArith Lia.
From Machine Require Import execution.WordSemantics execution.LinkedCalls execution.LinkedRun execution.ScalarWords
 execution.VectorProcedure memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.KeyTable Require Image.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require RowProduct EligibleLanes TableEntry TableFrame TableIdentity TableMultiple TableProduct.
Local Open Scope Z_scope.

Local Opaque TableEntry.enter TableFrame.enter TableIdentity.fill TableMultiple.start TableProduct.execute
 Power.apply_kernel DecoderProduct.kernel.

Definition execute bias:procedure:=then_run (TableEntry.enter bias)
 (then_run (TableFrame.enter bias) (then_run (TableIdentity.fill bias)
  (then_run (TableMultiple.start bias) (TableProduct.execute bias)))).
Record result pol bias e p q:Prop:=Result {
 address:ip q=TableFrame.base bias+259;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 arguments:TableMultiple.pointers pol e 1 (machine q);
 constants:forall j i,(i<4)%nat -> vectors(machine q) j (28+i)%nat=DecoderFrame.constant i;
 point_after:preserved (span (TableEntry.point e) 1280) (mem(machine p)) (mem(machine q));
 rows:forall j i,(j<8)%nat -> 0<=i<20 ->
  read_word (mem(machine q)) (TableIdentity.center (TableIdentity.first e) j+8*i)=Image.identity_word i;
 product:forall j i,(j<8)%nat -> (i<5)%nat -> vectors(machine q) j i=TableProduct.two_dt e (machine p) j i;
 parent:TableParentFrame.retained pol bias e (machine p) (machine q)
}.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem checked pol bias e before p : placement e -> loaded pol bias (mem e) (writable e) ->
 EligibleLanes.post pol bias e before p -> regs(machine p) 14%nat<>0 ->
 exists q,execute bias p=Some q /\ result pol bias e p q.
Proof.
 intros P I E Live.
 destruct(TableEntry.checked _ _ _ _ _ P I E Live) as [a [Call A]].
 destruct(TableFrame.checked _ _ _ _ _ P I A) as [b [Frame B]].
 destruct(TableIdentity.checked _ _ _ _ _ P I B) as [c [Identity C]].
 destruct(TableMultiple.first _ _ _ _ _ _ P I B C) as [d [First D]].
 destruct(TableProduct.checked _ _ _ _ _ _ P I D) as [q [Product Q]].
 assert (Input:preserved (span (TableEntry.point e) 1280) (mem(machine p)) (mem(machine d))).
 { rewrite (TableMultiple.flat _ _ _ _ _ _ D).
   intros x X;rewrite (TableIdentity.surrounding _ _ _ _ _ C).
     2:{ intros [r [_ Hit]];unfold TableIdentity.center,TableIdentity.first,TableEntry.tables,TableEntry.point,span in *;lia. }
     rewrite (TableFrame.memory_after _ _ _ _ _ B),outside_spill,(TableEntry.memory_after _ _ _ _ _ A).
     * unfold store_word;apply write_outside;pose proof(scratch_stack _ P) as Apart;
       unfold disjoint,span,TableEntry.frame,TableEntry.point,common_top,Rows.frame,sp in *;destruct pol;lia.
     * change (Z.of_nat(length TableFrame.saved_regs)) with 6;pose proof(scratch_stack _ P) as Apart;
       unfold disjoint,span,TableEntry.frame,TableEntry.point,common_top,Rows.frame,sp in *;destruct pol;lia. }
 assert (Stack:forall x,span (scratch e) 25344 x -> ~(TableProduct.frame pol e-24<=x<TableProduct.frame pol e)).
 { intros x X;pose proof(scratch_stack _ P) as Apart.
   unfold TableProduct.frame,KeyTable.Frame.staging,KeyTable.Frame.align64,KeyTable.Frame.allocation;
   change KeyTable.Frame.saved_size with 48;pose proof(Z.mod_pos_bound (TableEntry.frame pol e-48) 64 ltac:(lia)).
   unfold span,disjoint,TableEntry.frame,common_top,Rows.frame,sp in *;destruct pol;lia. }
 exists q;split;[unfold execute,then_run;rewrite Call;cbn [bind];rewrite Frame;cbn [bind];rewrite Identity;
    cbn [bind];rewrite First;exact Product|constructor].
 - exact (TableProduct.address _ _ _ _ _ _ Q).
 - exact (TableProduct.writes _ _ _ _ _ _ Q).
 - exact (TableProduct.words _ _ _ _ _ _ Q).
 - exact (TableProduct.arguments _ _ _ _ _ _ Q).
 - exact (TableProduct.constants _ _ _ _ _ _ Q).
 - intros x X;rewrite (TableProduct.outside _ _ _ _ _ _ Q);[apply Input,X|apply Stack;unfold span,TableEntry.point in *;lia].
 - intros j i J N;rewrite <- (TableIdentity.finished_rows _ _ _ _ _ C j i J N).
   apply preserved_read with (outside:=span (scratch e) 25344).
   + intros x X;rewrite (TableProduct.outside _ _ _ _ _ _ Q),(TableMultiple.flat _ _ _ _ _ _ D);[reflexivity|].
     exact (Stack _ X).
   + intros k K;change (0<=k<8) in K;unfold span,TableIdentity.center,TableIdentity.first,TableEntry.tables;lia.
 - intros j i J N;rewrite (TableProduct.limbs _ _ _ _ _ _ Q j i N).
   unfold TableProduct.two_dt;apply RowProduct.ext;[|intros;reflexivity].
   intros k K;unfold TableProduct.field,TableOperands.inputs.
   apply preserved_read with (outside:=span (TableEntry.point e) 1280).
   + exact Input.
   + intros v V;change (0<=v<8) in V;unfold span;lia.
 - intros x K;rewrite (TableProduct.outside _ _ _ _ _ _ Q),(TableMultiple.flat _ _ _ _ _ _ D),
     (TableIdentity.surrounding _ _ _ _ _ C),(TableParentFrame.prologue _ _ _ _ _ _ A B).
   + reflexivity.
   + exact (TableParentFrame.identities _ _ _ K).
   + destruct K as [StackArea _];change (~span (TableProduct.frame pol e-1360) 2320 x) in StackArea;unfold span in StackArea;lia.
Qed.
End Iteration.
