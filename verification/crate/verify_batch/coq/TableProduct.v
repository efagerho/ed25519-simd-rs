From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.ScalarWords
 execution.VectorProcedure memory.ByteMemory memory.FlatMemory.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd.KeyTable Require Fields Frame.
From Ed25519Simd.Decode Require Power Kernels.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require TableEntry TableFrame TableMultiple TableKernels TableOperands DecoderProduct.
Local Open Scope Z_scope.

Definition execute bias:=then_run (TableOperands.setup bias) (TableKernels.call bias Fields.TwoDT).
Definition frame pol e:=KeyTable.Frame.staging(TableEntry.frame pol e).
Definition field e s j:=TableOperands.inputs (TableEntry.point e) s j.
Definition two_dt e s j:=Power.apply_kernel DecoderProduct.kernel Kernels.Multiply (field e s j) Fields.two_d.
Record result pol bias e digit p q:Prop:=Result {
 address:ip q=TableFrame.base bias+259;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 arguments:TableMultiple.pointers pol e digit (machine q);
 registers:forall r,regs(machine q) r=regs(machine p) r;
 outside:preserved (fun x=>~(frame pol e-24<=x<frame pol e)) (mem(machine p)) (mem(machine q));
 limbs:forall j i,(i<5)%nat -> vectors(machine q) j i=two_dt e (machine p) j i
}.
Theorem checked pol bias e digit before p : placement e -> loaded pol bias (mem e) (writable e) ->
 TableMultiple.positioned pol bias e digit before p -> exists q,execute bias p=Some q /\ result pol bias e digit p q.
Proof.
 intros P I E;pose proof(TableMultiple.arguments _ _ _ _ _ _ E) as Args.
 destruct(TableOperands.checked _ _ _ _ P I (TableMultiple.address _ _ _ _ _ _ E)
  (TableMultiple.writes _ _ _ _ _ _ E) (TableMultiple.words _ _ _ _ _ _ E) (TableMultiple.source _ _ _ _ Args))
  as [s [Setup [PC [Acc [W Inputs]]]]].
 pose proof(TableOperands.regs_after _ _ _ Inputs) as G.
 assert (SP:regs(machine s) 4%nat=frame pol e) by (rewrite G;exact (TableMultiple.stack _ _ _ _ Args)).
 assert (Space:room (DecoderProduct.area e) 24 (machine s)).
 { unfold room,DecoderProduct.area;cbn [bottom ceiling];rewrite SP;unfold frame,KeyTable.Frame.staging,
   KeyTable.Frame.align64,KeyTable.Frame.allocation;change KeyTable.Frame.saved_size with 48.
   pose proof(Z.mod_pos_bound (TableEntry.frame pol e-48) 64 ltac:(lia)).
   unfold TableEntry.frame,BatchScalar.common_top,Rows.frame,Return.sp in *;destruct pol;lia. }
 destruct(TableKernels.checked _ _ _ Fields.TwoDT P I s PC Acc Space) as [q [Call Effects]].
 destruct Effects as [End Paid Reg Keep V];exists q;split;[unfold execute,then_run;now rewrite Setup|constructor].
 - exact End.
 - exact Paid.
 - exact (TableKernels.preserves_words _ _ _ _ W Call).
 - destruct Args;constructor;rewrite Reg,G;assumption.
 - intro r;now rewrite Reg,G.
 - intros x X;rewrite Keep by (rewrite SP;exact X);now rewrite (TableOperands.memory_after _ _ _ Inputs).
 - intros j i N;rewrite (V j);apply DecoderProduct.lane_product.
   + intros k B;split;[exact (TableOperands.coordinates _ _ _ Inputs j k B)|exact (TableOperands.coefficient _ _ _ Inputs j k B)].
   + intros k B;exact (TableOperands.field_constants _ _ _ Inputs j k B).
   + exact N.
Qed.
