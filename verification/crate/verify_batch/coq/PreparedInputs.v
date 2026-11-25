From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require EligibleLanes PrepareOutputs PreparedFrame.
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

Lemma through_tables pol bias e caller p q : placement e -> PrepareOutputs.result pol bias e caller p q ->
 preserved (prefix e) (mem(machine caller)) (mem(machine q)).
Proof.
 intros P A x X;pose proof(scratch_stack _ P) as Apart;unfold prefix in X;unfold disjoint in Apart.
 rewrite (PrepareOutputs.surrounding _ _ _ _ _ _ A) by (unfold PrepareOutputs.dest,span,Rows.frame,sp in *;lia).
 rewrite (TableUnwind.parent _ _ _ _ _ (PrepareOutputs.parent _ _ _ _ _ _ A)).
 - unfold TableParentFrame.expected;rewrite outside_spill by (change (Z.of_nat(length TableFrame.saved_regs)) with 6;unfold TableEntry.frame,common_top,Rows.frame,sp in *;destruct pol;lia).
   apply write_outside;unfold TableEntry.frame,common_top,Rows.frame,sp in *;destruct pol;lia.
 - unfold TableParentFrame.keep,TableParentFrame.top,KeyTable.Frame.staging,KeyTable.Frame.allocation,KeyTable.Frame.align64.
   change KeyTable.Frame.saved_size with 48;pose proof(Z.mod_pos_bound (TableEntry.frame pol e-48) 64 ltac:(lia)).
   unfold TableEntry.point,TableEntry.tables,TableEntry.frame,common_top,Rows.frame,sp,span in *;destruct pol;intuition lia.
Qed.
