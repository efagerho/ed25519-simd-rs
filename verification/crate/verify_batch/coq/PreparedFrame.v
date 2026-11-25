From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun abi.SysV memory.FlatMemory memory.ByteMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require EligibilityFrame PrepareOutputs.
Local Open Scope Z_scope.

(* From the builder's return word upwards the preparation caller owns the
   live stack. The two output stores occupy exactly the pointer row and flags. *)
Definition kept pol e x:=common_top pol e-104<=x<sp e+8 /\ ~span (PrepareOutputs.dest e) 72 x.
Lemma retained pol bias e caller p q : placement e -> PrepareOutputs.result pol bias e caller p q ->
 preserved (kept pol e) (mem(machine caller)) (mem(machine q)).
Proof.
 intros P Q x [[Low High] Outside];rewrite (PrepareOutputs.surrounding _ _ _ _ _ _ Q x Outside).
 pose proof(TableUnwind.parent _ _ _ _ _ (PrepareOutputs.parent _ _ _ _ _ _ Q)) as Frame.
 rewrite Frame.
 - unfold TableParentFrame.expected;rewrite outside_spill by (unfold TableEntry.frame;lia).
   apply write_outside;unfold TableEntry.frame;lia.
 - unfold TableParentFrame.keep,TableParentFrame.top,KeyTable.Frame.staging,KeyTable.Frame.allocation,KeyTable.Frame.align64.
   change KeyTable.Frame.saved_size with 48;pose proof(Z.mod_pos_bound (TableEntry.frame pol e-48) 64 ltac:(lia)).
   pose proof(scratch_stack _ P) as Apart;unfold TableEntry.point,TableEntry.tables,TableEntry.frame,span,disjoint,common_top,Rows.frame,sp in *;
   destruct pol;intuition lia.
Qed.

Lemma context pol bias outer e caller p q : placement e -> PrepareOutputs.result pol bias e caller p q ->
 EligibilityFrame.context pol bias outer e caller -> EligibilityFrame.context pol bias outer e q.
Proof.
 intros P Q [Links Outputs Meta [Slots BP] Layout];pose proof(retained _ _ _ _ _ _ P Q) as Same. constructor.
 - eapply slots_preserved;[|exact Links];intros x X;apply Same;unfold kept,PrepareOutputs.dest,span,common_top,Rows.frame,sp in *;destruct pol;lia.
 - eapply keep_saved_outputs;[|exact Outputs];intros x X;apply Same;unfold kept,PrepareOutputs.dest,span,common_top,Rows.frame,sp in *;destruct pol;lia.
 - eapply IndexStores.metadata_preserved;[|exact Meta];intros x X;apply Same;unfold kept,PrepareOutputs.dest,span,common_top,Rows.frame,sp in *;destruct pol;lia.
 - split;[intros x X;rewrite Same;[apply Slots,X|unfold kept,PrepareOutputs.dest,span,common_top,Rows.frame,sp in *;destruct pol;lia]|].
   rewrite (PrepareOutputs.registers _ _ _ _ _ _ Q),(TableUnwind.registers _ _ _ _ _ (PrepareOutputs.parent _ _ _ _ _ _ Q)) by (cbn;tauto);exact BP.
 - eapply WrapperInputs.preserve;[|exact Layout];intros x X;apply Same;unfold kept,PrepareOutputs.dest,WrapperInputs.needed,span,common_top,Rows.frame,sp in *;destruct pol;lia.
Qed.

Lemma sig_byte pol bias e caller p q : placement e -> PrepareOutputs.result pol bias e caller p q ->
 mem(machine q)(Rows.frame e+840)=mem(machine caller)(Rows.frame e+840).
Proof.
 intros P Q;apply (retained _ _ _ _ _ _ P Q);unfold kept,PrepareOutputs.dest,span,common_top,Rows.frame,sp;destruct pol;lia.
Qed.
