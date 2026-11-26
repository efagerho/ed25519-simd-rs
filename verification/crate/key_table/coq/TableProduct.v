From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.ScalarWords
 execution.VectorProcedure memory.ByteMemory memory.FlatMemory.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd.KeyTable Require Fields Frame.
From Ed25519Simd.Decode Require Power Kernels.
From Ed25519Simd.KeyTable Require TableMultiple TableKernels TableOperands.
From Ed25519Simd.KeyTable Require Import CallLayout.
From Ed25519Simd.Decode Require NativeProduct FieldLiterals.
Local Open Scope Z_scope.

Definition execute bias:=then_run (TableOperands.setup bias) (TableKernels.call bias Fields.TwoDT).
Definition field e s j:=TableOperands.inputs (CallLayout.point_ptr e) s j.
Definition two_dt e s j:=Power.apply_kernel NativeProduct.kernel Kernels.Multiply (field e s j) Fields.two_d.
Record result (root:cpu) bias e digit p q:Prop:=Result {
 address:ip q=CallLayout.base bias+259;
 writes:accounted root (writable e) q;
 words:well_formed(machine q);
 arguments:TableMultiple.pointers e digit (machine q);
 registers:forall r,regs(machine q) r=regs(machine p) r;
 outside:preserved (fun x=>~(CallLayout.stage e-24<=x<CallLayout.stage e)) (mem(machine p)) (mem(machine q));
 constants:forall j i,(i<4)%nat -> vectors(machine q) j (28+i)%nat=FieldLiterals.constant i;
 limbs:forall j i,(i<5)%nat -> vectors(machine q) j i=two_dt e (machine p) j i
}.
Theorem checked (root:cpu) bias e digit before p : placement e -> loaded root bias e ->
 TableMultiple.positioned root bias e digit before p -> exists q,execute bias p=Some q /\ result root bias e digit p q.
Proof.
 intros P I E;pose proof(TableMultiple.arguments _ _ _ _ _ _ E) as Args.
 destruct(TableOperands.checked _ _ _ _ P I (TableMultiple.address _ _ _ _ _ _ E)
  (TableMultiple.writes _ _ _ _ _ _ E) (TableMultiple.words _ _ _ _ _ _ E) (TableMultiple.source _ _ _ Args))
  as [s [Setup [PC [Acc [W Inputs]]]]].
 pose proof(TableOperands.regs_after _ _ _ _ Inputs) as G.
 assert (SP:regs(machine s) 4%nat=CallLayout.stage e) by (rewrite G;exact (TableMultiple.stack _ _ _ Args)).
 assert (Space:room (CallLayout.stack_area e) 24 (machine s)).
 { unfold room,CallLayout.stack_area;cbn [bottom ceiling];rewrite SP.
   pose proof(CallLayout.depth e P);lia. }
 destruct(TableKernels.checked _ _ _ Fields.TwoDT P I s PC Acc Space) as [q [Call Effects]].
 destruct Effects as [End Paid Reg Keep V];exists q;split;[unfold execute,then_run;now rewrite Setup|constructor].
 - exact End.
 - exact Paid.
 - exact (TableKernels.preserves_words _ _ _ _ W Call).
 - destruct Args;constructor;rewrite Reg,G;assumption.
 - intro r;now rewrite Reg,G.
 - intros x X;rewrite Keep by (rewrite SP;exact X);now rewrite (TableOperands.memory_after _ _ _ _ Inputs).
 - intros j i N;rewrite (V j);destruct((proj2 NativeProduct.multiplication) no_read no_read
      (vectors(machine s) j) (vectors(machine s) j) ltac:(reflexivity)) as [_ High].
   rewrite High by lia;exact (TableOperands.field_constants _ _ _ _ Inputs j i N).
 - intros j i N;rewrite (V j);apply NativeProduct.lane_product.
   + intros k B;split;[exact (TableOperands.coordinates _ _ _ _ Inputs j k B)|exact (TableOperands.coefficient _ _ _ _ Inputs j k B)].
   + intros k B;exact (TableOperands.field_constants _ _ _ _ Inputs j k B).
   + exact N.
Qed.
