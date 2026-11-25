From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.VectorProcedure
 memory.ByteMemory memory.FlatMemory.
From Ed25519Simd.KeyTable Require Fields.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require TableFrame TableEntry TableMultiple TableProduct TableLinear TableColumn.
Local Open Scope Z_scope.
Definition start bias:=then_run (TableColumn.execute bias Fields.Difference)
 (then_run (TableColumn.execute bias Fields.Sum) (TableColumn.execute bias Fields.Twice)).
Definition frame pol e x:=~(TableProduct.frame pol e-8<=x<TableProduct.frame pol e).
Lemma apart pol e x : placement e -> span (scratch e) 25344 x -> frame pol e x.
Proof.
 intros P X;pose proof(scratch_stack _ P) as S;unfold frame,TableProduct.frame,KeyTable.Frame.staging,KeyTable.Frame.align64,
 KeyTable.Frame.allocation;change KeyTable.Frame.saved_size with 48;pose proof(Z.mod_pos_bound (TableEntry.frame pol e-48) 64 ltac:(lia)).
 unfold TableEntry.frame,common_top,Rows.frame,sp,disjoint,span in *;destruct pol;lia.
Qed.

Lemma point_value e f s t j : (j<8)%nat -> preserved (span (TableEntry.point e) 1280) (mem s) (mem t) ->
 forall i,TableColumn.value f e t j i=TableColumn.value f e s j i.
Proof.
 intros J Keep;assert (Input:forall c k,(c<4)%nat -> (k<5)%nat -> TableColumn.coord e t j c k=TableColumn.coord e s j c k).
 { intros c k C K;unfold TableColumn.coord;apply preserved_read with (outside:=span (TableEntry.point e) 1280);[exact Keep|].
   intros l B;change (0<=l<8) in B;unfold span;lia. }
 destruct f;intro i;unfold TableColumn.value;cbn [TableLinear.operation Fields.compute Fields.rhs Fields.source Fields.linear_op];
 unfold Fields.linear_result.
 all: apply Instructions.run_ext;[reflexivity|];intro k;unfold Power.feed;destruct(Kernels.constant k);[reflexivity|];
   destruct (Nat.ltb_spec k 5);[apply Input;lia|];destruct (Nat.ltb_spec k 10);[apply Input;lia|reflexivity].
Qed.

Lemma same_value pol e f s t j : placement e -> (j<8)%nat -> preserved (frame pol e) (mem s) (mem t) ->
 forall i,TableColumn.value f e t j i=TableColumn.value f e s j i.
Proof. intros P J M;apply point_value;[exact J|intros x X;apply M,apart;[exact P|unfold span,TableEntry.point in *;lia]]. Qed.

Record columns e s t:Prop:=Columns {
 product:forall j i,(i<5)%nat -> vectors t j (5+i)%nat=vectors s j i;
 difference:forall j i,(j<8)%nat -> (i<5)%nat -> vectors t j (16+i)%nat=TableColumn.value Fields.Difference e s j i;
 sum:forall j i,(j<8)%nat -> (i<5)%nat -> vectors t j (21+i)%nat=TableColumn.value Fields.Sum e s j i;
 twice:forall j i,(j<8)%nat -> (i<5)%nat -> vectors t j i=TableColumn.value Fields.Twice e s j i
}.

Lemma keep_constants f e s t : TableColumn.column f e s t -> TableColumn.constants s -> TableColumn.constants t.
Proof.
 intros E C j i N;rewrite (TableColumn.other _ _ _ _ E);[apply C,N|unfold TableLinear.reserved;
 rewrite (proj2 (Nat.leb_le 16 (28+i)) ltac:(lia)),Bool.orb_true_r;reflexivity|destruct f;cbn [TableLinear.save_register];lia].
Qed.
Theorem checked pol bias e digit p : placement e -> loaded pol bias (mem e) (writable e) ->
 ip p=TableFrame.base bias+259 -> accounted e (writable e) p -> well_formed(machine p) ->
 TableMultiple.pointers pol e digit (machine p) -> TableColumn.constants(machine p) ->
 exists q,start bias p=Some q /\ ip q=TableFrame.base bias+622 /\ accounted e (writable e) q /\ well_formed(machine q) /\
 (forall r,regs(machine q) r=regs(machine p) r) /\ preserved (frame pol e) (mem(machine p)) (mem(machine q)) /\ columns e (machine p) (machine q).
Proof.
 intros P I PC Acc W Ptr C;pose proof(TableMultiple.source _ _ _ _ Ptr) as R12;pose proof(TableMultiple.stack _ _ _ _ Ptr) as SP.
 destruct(TableColumn.checked pol bias e Fields.Difference p P I PC Acc W R12 SP C)
  as [a [A [At [Paid [AW [GA [MA DA]]]]]]].
 destruct(TableColumn.checked pol bias e Fields.Sum a P I At Paid AW ltac:(now rewrite GA) ltac:(now rewrite GA)
   (keep_constants _ _ _ _ DA C)) as [b [B [Bt [Safe [BW [GB [MB SB]]]]]]].
 destruct(TableColumn.checked pol bias e Fields.Twice b P I Bt Safe BW ltac:(now rewrite GB,GA) ltac:(now rewrite GB,GA)
   (keep_constants _ _ _ _ SB (keep_constants _ _ _ _ DA C))) as [q [R [End [Done [QW [G [M T]]]]]]].
 exists q;split;[unfold start,then_run;rewrite A;cbn [bind];rewrite B;exact R|].
 split;[exact End|split;[exact Done|split;[exact QW|split;[intro r;now rewrite G,GB,GA|split]]]].
 - intros x X;now rewrite M,MB,MA.
 - constructor.
   + intros j i N;rewrite (TableColumn.other _ _ _ _ T),(TableColumn.other _ _ _ _ SB).
     * exact (TableColumn.saved _ _ _ _ DA j i N).
     * unfold TableLinear.reserved;destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity.
     * cbn [TableLinear.save_register];lia.
     * unfold TableLinear.reserved;destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity.
     * cbn [TableLinear.save_register];lia.
   + intros j i J N;rewrite (TableColumn.other _ _ _ _ T).
     * exact (eq_trans (TableColumn.saved _ _ _ _ SB j i N) (TableColumn.limbs _ _ _ _ DA j i N)).
     * unfold TableLinear.reserved;rewrite (proj2(Nat.leb_le 16 (16+i)) ltac:(lia)),Bool.orb_true_r;reflexivity.
     * cbn [TableLinear.save_register];lia.
   + intros j i J N;exact (eq_trans (TableColumn.saved _ _ _ _ T j i N) (eq_trans (TableColumn.limbs _ _ _ _ SB j i N) (same_value pol _ _ _ _ _ P J MA i))).
   + intros j i J N;rewrite (TableColumn.limbs _ _ _ _ T j i N).
     apply (same_value pol _ _ _ _ _ P J);intros x X;now rewrite MB,MA.
Qed.
