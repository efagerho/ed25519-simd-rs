From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.VectorProcedure memory.ByteMemory.
From Ed25519Simd.KeyTable Require Fields Image.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require EligibleLanes TableStart TableColumn TableCoordinates TableFrame.
Local Open Scope Z_scope.
Definition execute bias:=then_run (TableStart.execute bias) (TableCoordinates.start bias).
Record result pol bias e p q:Prop:=Result {
 address:ip q=TableFrame.base bias+622;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 arguments:TableMultiple.pointers pol e 1 (machine q);
 rows:forall j i,(j<8)%nat -> 0<=i<20 ->
  read_word (mem(machine q)) (TableIdentity.center (TableIdentity.first e) j+8*i)=Image.identity_word i;
 fields:forall j i,(j<8)%nat -> (i<5)%nat ->
  vectors(machine q) j (5+i)%nat=TableProduct.two_dt e (machine p) j i /\
  vectors(machine q) j (16+i)%nat=TableColumn.value Fields.Difference e (machine p) j i /\
  vectors(machine q) j (21+i)%nat=TableColumn.value Fields.Sum e (machine p) j i /\
  vectors(machine q) j i=TableColumn.value Fields.Twice e (machine p) j i;
 parent:TableParentFrame.retained pol bias e (machine p) (machine q)
}.
Theorem checked pol bias e before p : placement e -> loaded pol bias (mem e) (writable e) ->
 EligibleLanes.post pol bias e before p -> regs(machine p) 14%nat<>0 ->
 exists q,execute bias p=Some q /\ result pol bias e p q.
Proof.
 intros P I E Live;destruct(TableStart.checked _ _ _ _ _ P I E Live) as [a [Start A]].
 destruct(TableCoordinates.checked _ _ _ _ _ P I (TableStart.address _ _ _ _ _ A) (TableStart.writes _ _ _ _ _ A)
  (TableStart.words _ _ _ _ _ A) (TableStart.arguments _ _ _ _ _ A) (TableStart.constants _ _ _ _ _ A))
  as [q [Run [PC [Paid [W [G [M C]]]]]]].
 exists q;split;[unfold execute,then_run;now rewrite Start|constructor].
 - exact PC.
 - exact Paid.
 - exact W.
 - destruct(TableStart.arguments _ _ _ _ _ A);constructor;now rewrite G.
 - intros j i J N;rewrite <- (TableStart.rows _ _ _ _ _ A j i J N);apply preserved_read with (outside:=TableCoordinates.frame pol e);[exact M|].
   intros k K;change (0<=k<8) in K;apply TableCoordinates.apart;[exact P|unfold span,TableIdentity.center,TableIdentity.first,TableEntry.tables;lia].
 - intros j i J N;pose proof(TableStart.point_after _ _ _ _ _ A) as Kept;repeat split.
   + rewrite (TableCoordinates.product _ _ _ C j i N);apply (TableStart.product _ _ _ _ _ A);assumption.
   + rewrite (TableCoordinates.difference _ _ _ C j i J N);apply TableCoordinates.point_value;assumption.
   + rewrite (TableCoordinates.sum _ _ _ C j i J N);apply TableCoordinates.point_value;assumption.
   + rewrite (TableCoordinates.twice _ _ _ C j i J N);apply TableCoordinates.point_value;assumption.
 - intros x K;rewrite M;[exact (TableStart.parent _ _ _ _ _ A x K)|].
   destruct K as [Area _];change (~span (TableProduct.frame pol e-1360) 2320 x) in Area;unfold TableCoordinates.frame,span in *;lia.
Qed.
