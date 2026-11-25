From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require EligibleLanes PrepareOutputs PreparedFrame DecodedSignature.
From Ed25519Simd.SignatureScalar Require Audit.
From Curve25519 Require Import Scalar.
From ProofArithmetic Require Import Radix.
Local Open Scope Z_scope.

(* The decoder writes the two points above the encodings and digits. The
   table builder also borrows the key point, but neither borrows this prefix. *)
Definition prefix e x:=scratch e<=x<scratch e+1024.
Definition encodings e s:=PrepareCopies.staged (mem e) (mem s) (scratch e) (ScalarInputs.encoding_ptr e) 8.

Lemma keep_encodings e s t : preserved (prefix e) (mem s) (mem t) -> encodings e s -> encodings e t.
Proof. intros M H j sig k J K;rewrite M;[apply H;assumption|unfold prefix,PrepareCopies.dest;destruct sig;lia]. Qed.

Lemma through_decoder pol bias e d t : placement e -> EligibleLanes.checked_trace pol bias e d t ->
 preserved (prefix e) (mem(machine d)) (mem(machine(EligibleLanes.stopped t))).
Proof.
 intros P [D E] x X;rewrite (EligibleLanes.memory_after _ _ _ _ _ E);unfold EligibleLanes.store_at,commit;cbn [size address payload].
 pose proof(scratch_stack _ P) as Apart;unfold prefix in X;unfold disjoint in Apart.
 rewrite write_outside by (unfold Rows.frame,sp in *;lia).
 apply (DecoderReturn.caller_memory _ _ _ _ _ D);unfold DecoderSpills.caller_byte,DecoderSpills.top.
 split;[unfold common_top,Rows.frame,sp in *;destruct pol;lia|].
 intros sig;unfold BatchDecode.point,BatchDecode.point_offset,span;destruct sig;lia.
Qed.

Definition digits e s:=forall j,(j<8)%nat ->
 let x:=ScalarInputs.original_scalar e (TailCopy.row_index e j) in
 let ds:=SignatureScalar.Audit.digits s (scratch e+512) j in
 if x <? L then Forall (fun d=> -8<=d<8) ds /\ number 16 ds=x else ds=repeat 0 64.

Lemma keep_digits e s t : preserved (span (scratch e+512) 512) (mem s) (mem t) -> digits e s -> digits e t.
Proof.
 intros M D j J;specialize(D j J);cbv zeta in D|-*.
 assert (E:SignatureScalar.Audit.digits t (scratch e+512) j=SignatureScalar.Audit.digits s (scratch e+512) j).
 { unfold SignatureScalar.Audit.digits;apply map_ext_in;intros k K;apply in_seq in K;rewrite M;[reflexivity|unfold span;lia]. }
 now rewrite E.
Qed.

Definition signature e s:=DecodedRows.geometry true e (DecodedRows.buffer true e s).
Record operands e s:Prop:=Operands { encoded:encodings e s; scalar_digits:digits e s; signature_point:signature e s }.
Definition operand_bytes e x:=prefix e x \/ span (BatchDecode.point e true) 1280 x.
Lemma keep e s t : preserved (operand_bytes e) (mem s) (mem t) -> operands e s -> operands e t.
Proof.
 intros M [Enc D R];constructor.
 - eapply keep_encodings;[|exact Enc];intros x X;apply M;left;exact X.
 - eapply keep_digits;[|exact D];intros x X;apply M;left;unfold prefix,span in *;lia.
 - eapply DecodedRows.keep;[|exact R];intros x X;apply M;right;exact X.
Qed.

Theorem from_decoder pol bias e scalar d t : placement e -> ScalarInputs.recoded e (machine scalar) ->
 BatchDecode.handoff pol e scalar d -> encodings e (machine d) -> EligibleLanes.checked_trace pol bias e d t ->
 operands e (machine(EligibleLanes.stopped t)).
Proof.
 intros P S H Enc C;pose proof(through_decoder _ _ _ _ _ P C) as M;destruct C as [D E];constructor.
 - exact (keep_encodings _ _ _ M Enc).
 - eapply (keep_digits e (machine scalar));[|intros j J;exact (proj2(proj2 S j J))].
   intros x X;unfold span in X;rewrite M by (unfold prefix;lia);apply (BatchDecode.kept_bytes _ _ _ _ H).
   destruct(scratch_stack _ P);unfold span,disjoint,common_top,Rows.frame,sp in *;destruct pol;lia.
 - apply (DecodedRows.keep true e (machine(PairReturn.returned(DecoderReturn.points(EligibleLanes.decoded t))))).
   + intros x X;rewrite (EligibleLanes.memory_after _ _ _ _ _ E);unfold EligibleLanes.store_at,commit;cbn [size address payload].
     rewrite write_outside,(DecoderReturn.memory_after _ _ _ _ _ D);[reflexivity|].
     destruct(scratch_stack _ P);unfold BatchDecode.point,BatchDecode.point_offset,span,disjoint,Rows.frame,sp in *;lia.
   + exact (DecodedSignature.checked _ _ _ _ P (DecoderReturn.decoded _ _ _ _ _ D)).
Qed.

Lemma through_tables pol bias e caller p q : placement e -> PrepareOutputs.result pol bias e caller p q ->
 preserved (operand_bytes e) (mem(machine caller)) (mem(machine q)).
Proof.
 intros P A x X;pose proof(scratch_stack _ P) as Apart;unfold operand_bytes,prefix,BatchDecode.point,BatchDecode.point_offset,span in X;unfold disjoint in Apart.
 rewrite (PrepareOutputs.surrounding _ _ _ _ _ _ A) by (unfold PrepareOutputs.dest,span,Rows.frame,sp in *;lia).
 rewrite (TableUnwind.parent _ _ _ _ _ (PrepareOutputs.parent _ _ _ _ _ _ A)).
 - unfold TableParentFrame.expected;rewrite outside_spill by (change (Z.of_nat(length TableFrame.saved_regs)) with 6;unfold TableEntry.frame,common_top,Rows.frame,sp in *;destruct pol;lia).
   apply write_outside;unfold TableEntry.frame,common_top,Rows.frame,sp in *;destruct pol;lia.
 - unfold TableParentFrame.keep,TableParentFrame.top,KeyTable.Frame.staging,KeyTable.Frame.allocation,KeyTable.Frame.align64.
   change KeyTable.Frame.saved_size with 48;pose proof(Z.mod_pos_bound (TableEntry.frame pol e-48) 64 ltac:(lia)).
   unfold TableEntry.point,TableEntry.tables,TableEntry.frame,common_top,Rows.frame,sp,span in *;destruct pol;intuition lia.
Qed.
