From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.VectorProcedure memory.ByteMemory memory.FlatMemory.
From Ed25519Simd.KeyTable Require Image Fields.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require EligibleLanes TableValues TableStage TableTranspose.
Local Open Scope Z_scope.
Local Opaque TableColumn.value TableProduct.two_dt TableStage.execute TableValues.execute TableTranspose.execute.

Definition column e s j i:=if (i<?5)%nat then TableColumn.value Fields.Difference e s j i
 else if (i<?10)%nat then TableColumn.value Fields.Sum e s j (i-5)%nat
 else if (i<?15)%nat then TableProduct.two_dt e s j (i-10)%nat else TableColumn.value Fields.Twice e s j (i-15)%nat.
Lemma from_fields e s t :
 (forall j i,(j<8)%nat -> (i<5)%nat ->
  vectors t j (5+i)%nat=TableProduct.two_dt e s j i /\
  vectors t j (16+i)%nat=TableColumn.value Fields.Difference e s j i /\
  vectors t j (21+i)%nat=TableColumn.value Fields.Sum e s j i /\
  vectors t j i=TableColumn.value Fields.Twice e s j i) ->
 forall j i,(j<8)%nat -> (i<20)%nat -> vectors t j (Image.reg_for i)=column e s j i.
Proof.
 intros V j i J N;unfold column,Image.reg_for.
 destruct(Nat.ltb_spec i 5) as [Low|High].
 - rewrite (proj2(Nat.ltb_lt i 10) ltac:(lia));apply (proj1(proj2(V j i J Low))).
 - destruct(Nat.ltb_spec i 10) as [Sum|Upper].
   + replace (16+i)%nat with (21+(i-5))%nat by lia;apply (proj1(proj2(proj2(V j (i-5)%nat J ltac:(lia))))).
   + destruct(Nat.ltb_spec i 15) as [Product|Zed].
     * replace (i-5)%nat with (5+(i-10))%nat by lia;apply (proj1(V j (i-10)%nat J ltac:(lia))).
     * apply (proj2(proj2(proj2(V j (i-15)%nat J ltac:(lia))))).
Qed.

Lemma original pol bias e p q : TableValues.result pol bias e p q ->
 forall j i,(j<8)%nat -> (i<20)%nat -> vectors(machine q) j (Image.reg_for i)=column e (machine p) j i.
Proof. intro V;apply from_fields,(TableValues.fields _ _ _ _ _ V). Qed.

Definition index second i:=(if second:bool then 8+i else i)%nat.
Lemma reg_index b i : (i<8)%nat -> TableTranspose.reg b i=Image.reg_for (index b i).
Proof. intros N;destruct b;destruct i as [|[|[|[|[|[|[|[|i]]]]]]]];try lia;reflexivity. Qed.
Definition execute bias:=then_run (TableValues.execute bias) (then_run (TableStage.execute bias) (TableTranspose.execute bias)).
Record result pol bias e p q:Prop:=Result {
 address:ip q=TableFrame.base bias+1168;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 arguments:TableMultiple.pointers pol e 1 (machine q);
 rows:forall j i,(j<8)%nat -> 0<=i<20 ->
  read_word (mem(machine q)) (TableIdentity.center (TableIdentity.first e) j+8*i)=Image.identity_word i;
 staged:forall j i,(j<8)%nat -> (i<15)%nat -> read_word (mem(machine q))
  (TableProduct.frame pol e+64*Z.of_nat i+8*Z.of_nat j)=column e (machine p) j i;
 pair:forall b key i,(key<8)%nat -> (i<8)%nat -> vectors(machine q) i (TableTranspose.reg b key)=column e (machine p) key (index b i);
 tail:forall key i,(key<8)%nat -> (i<4)%nat -> vectors(machine q) key (1+i)%nat=column e (machine p) key (16+i)%nat
}.

Theorem checked pol bias e before p : placement e -> loaded pol bias (mem e) (writable e) ->
 EligibleLanes.post pol bias e before p -> regs(machine p) 14%nat<>0 ->
 exists q,execute bias p=Some q /\ result pol bias e p q.
Proof.
 intros P I E Live;destruct(TableValues.checked _ _ _ _ _ P I E Live) as [a [Values A]].
 pose proof(TableValues.arguments _ _ _ _ _ A) as Ptr.
 destruct(TableStage.checked _ _ _ 1 a P I ltac:(lia) (TableValues.address _ _ _ _ _ A) (TableValues.writes _ _ _ _ _ A)
  (TableValues.words _ _ _ _ _ A) (TableMultiple.multiple _ _ _ _ Ptr) (TableMultiple.count _ _ _ _ Ptr)
  (TableMultiple.stack _ _ _ _ Ptr)) as [b [Stage B]].
 destruct(TableTranspose.checked pol bias e b I (TableStage.address _ _ _ _ _ _ B) (TableStage.writes _ _ _ _ _ _ B)
  (TableStage.words _ _ _ _ _ _ B)) as [q [Transpose [End C]]].
 pose proof(TableStage.bank _ _ _ _ _ _ B) as V;pose proof(TableTranspose.memory_after _ _ _ C) as M.
 exists q;split;[unfold execute,then_run;rewrite Values;cbn [bind];rewrite Stage;exact Transpose|constructor].
 - exact End.
 - exact (TableTranspose.writes _ _ _ C).
 - exact (TableTranspose.words _ _ _ C).
 - destruct Ptr;constructor;rewrite (TableTranspose.registers _ _ _ C),(TableStage.registers _ _ _ _ _ _ B);assumption.
 - intros j i J N;rewrite M,<- (TableValues.rows _ _ _ _ _ A j i J N);apply preserved_read with (outside:=fun x=>~TableStage.buffer (TableProduct.frame pol e) x).
   + exact (TableStage.outside _ _ _ _ _ _ B).
   + intros k K;change (0<=k<8) in K;unfold TableStage.buffer,TableProduct.frame,KeyTable.Frame.staging,
     KeyTable.Frame.align64,KeyTable.Frame.allocation;change KeyTable.Frame.saved_size with 48.
     pose proof(Z.mod_pos_bound (TableEntry.frame pol e-48) 64 ltac:(lia));pose proof(scratch_stack _ P) as Apart.
     unfold TableIdentity.center,TableIdentity.first,TableEntry.tables,TableEntry.frame,common_top,Rows.frame,sp,disjoint in *;destruct pol;lia.
 - intros j i J N;rewrite M,(TableStage.positive _ _ _ _ _ _ B eq_refl i j N J);apply (original _ _ _ _ _ A);lia.
 - intros second key i K N;rewrite (TableTranspose.rows _ _ _ C second key i K N),V,reg_index by exact N.
   apply (original _ _ _ _ _ A);[exact K|destruct second;cbn [index];lia].
 - intros key i K N;rewrite (TableTranspose.tail_rows _ _ _ C i key N K),V.
   replace (1+i)%nat with (Image.reg_for (16+i)) by (destruct i as [|[|[|[|i]]]];try lia;reflexivity).
   apply (original _ _ _ _ _ A);lia.
Qed.
