From Coq Require Import ZArith List Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.VectorProcedure memory.FlatMemory memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.KeyTable Require Image Fields.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require TableSignedWords TableNextDigit TableAdd.
Local Open Scope Z_scope.

Definition execute bias p ks:=bind (TableProduct.execute bias p) (fun a=>
 bind (TableCoordinates.start bias a) (fun b=>bind (TableStage.execute bias b) (fun c=>
 bind (TableTranspose.execute bias c) (fun d=>bind (TablePackLiterals.execute bias d ks)
 (fun '(mask,bank)=>TablePacking.execute bias mask bank))))).
Definition preserved_byte pol e digit x:=
 ~(TableProduct.frame pol e-24<=x<TableProduct.frame pol e) /\ ~TablePackRows.area e digit x.
Record post pol bias e digit p q:Prop:=Post {
 address:ip q=TableFrame.base bias+1947;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 pointers:TableMultiple.pointers pol e digit (machine q);
 rows:TableSignedWords.signed e digit (TablePackedInputs.column e (machine p)) (machine q);
 outside:preserved (preserved_byte pol e digit) (mem(machine p)) (mem(machine q))
}.
Lemma elsewhere pol e s t : placement e ->
 preserved (fun x=>~(TableProduct.frame pol e-24<=x<TableProduct.frame pol e)) (mem s) (mem t) ->
 preserved (Return.span (TableEntry.point e) 1280) (mem s) (mem t).
Proof.
 intros P M x X;apply M;pose proof(scratch_stack _ P) as Apart;pose proof(TableAddLayout.stack pol e) as Depth;
 unfold TableAddLayout.stage in Depth;unfold TableEntry.point,span,disjoint in *;lia.
Qed.
Theorem checked pol bias e digit before p ks : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> 2<=digit<=8 -> TableMultiple.positioned pol bias e digit before p ->
 exists q bank,execute bias p ks=Some(q,bank) /\ post pol bias e digit p q.
Proof.
 intros P I Al N Init;destruct(TableProduct.checked _ _ _ _ _ _ P I Init) as [a [Product A]].
 destruct(TableCoordinates.checked _ _ _ _ _ P I (TableProduct.address _ _ _ _ _ _ A) (TableProduct.writes _ _ _ _ _ _ A)
  (TableProduct.words _ _ _ _ _ _ A) (TableProduct.arguments _ _ _ _ _ _ A) (TableProduct.constants _ _ _ _ _ _ A))
  as [b [Fields [PC [Acc [W [G [M Col]]]]]]].
 assert (PB:TableMultiple.pointers pol e digit (machine b)) by (destruct(TableProduct.arguments _ _ _ _ _ _ A);constructor;now rewrite G).
 assert (Values:forall j i,(j<8)%nat -> (i<20)%nat ->
  vectors(machine b) j (Image.reg_for i)=TablePackedInputs.column e (machine p) j i).
 { apply TablePackedInputs.from_fields;intros j i J L;split.
   - rewrite (TableCoordinates.product _ _ _ Col j i L);exact (TableProduct.limbs _ _ _ _ _ _ A j i L).
   - pose proof(elsewhere pol e _ _ P (TableProduct.outside _ _ _ _ _ _ A)) as Point;repeat split.
     + rewrite (TableCoordinates.difference _ _ _ Col j i J L);now apply TableCoordinates.point_value.
     + rewrite (TableCoordinates.sum _ _ _ Col j i J L);now apply TableCoordinates.point_value.
     + rewrite (TableCoordinates.twice _ _ _ Col j i J L);now apply TableCoordinates.point_value. }
 destruct(TableStage.checked _ _ _ digit b P I ltac:(lia) PC Acc W (TableMultiple.multiple _ _ _ _ PB) (TableMultiple.count _ _ _ _ PB)
    (TableMultiple.stack _ _ _ _ PB)) as [c [Stage C]].
 destruct(TableTranspose.checked pol bias e c I (TableStage.address _ _ _ _ _ _ C) (TableStage.writes _ _ _ _ _ _ C)
   (TableStage.words _ _ _ _ _ _ C)) as [d [Trans [DPC D]]].
 destruct(TablePackLiterals.checked pol bias e d ks I (TableMask.aligned _ Al) DPC (TableTranspose.writes _ _ _ D) (TableTranspose.words _ _ _ D))
   as [m [bank [Mask K]]].
 assert (Ptr:TableMultiple.pointers pol e digit (machine m)).
 { destruct PB;constructor;rewrite (TablePackLiterals.registers _ _ _ _ _ K);cbn [Instructions.put Nat.eqb];
   rewrite (TableTranspose.registers _ _ _ D),(TableStage.registers _ _ _ _ _ _ C);assumption. }
 destruct(TablePacking.checked pol bias e digit m bank P I ltac:(lia) (TablePackLiterals.address _ _ _ _ _ K) (TablePackLiterals.writes _ _ _ _ _ K)
   (TablePackLiterals.machine_words _ _ _ _ _ K) Ptr) as [q [Pack Q]].
 exists q,bank;split;[unfold execute;rewrite Product;cbn [bind];rewrite Fields;cbn [bind];rewrite Stage;cbn [bind];rewrite Trans;cbn [bind];rewrite Mask;exact Pack|constructor].
 - exact (TablePacking.address _ _ _ _ _ _ _ Q).
 - exact (TablePacking.writes _ _ _ _ _ _ _ Q).
 - exact (TablePacking.words _ _ _ _ _ _ _ Q).
 - exact (TablePacking.arguments _ _ _ _ _ _ _ Q).
 - assert (R:TablePackValues.represents (TablePackedInputs.column e (machine p)) TablePackValues.initial (machine m)).
   { apply TablePackValues.from_registers.
     - intros side j i J L;rewrite (TablePackLiterals.prior _ _ _ _ _ K).
       2:{ destruct side;destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];try lia;vm_compute;lia. }
       rewrite (TableTranspose.rows _ _ _ D side j i J L),(TableStage.bank _ _ _ _ _ _ C),TablePackedInputs.reg_index by exact L.
       apply Values;[exact J|destruct side;cbn [TablePackedInputs.index];lia].
     - intros j i J L;rewrite (TablePackLiterals.prior _ _ _ _ _ K) by lia;rewrite (TableTranspose.tail_rows _ _ _ D i j L J),(TableStage.bank _ _ _ _ _ _ C).
       replace (1+i)%nat with (Image.reg_for (16+i)) by (destruct i as [|[|[|[|i]]]];try lia;reflexivity);apply Values;lia.
     - exact (TablePackLiterals.literals _ _ _ _ _ K). }
   exact (TableSignedWords.contents pol bias e digit m q bank _ P ltac:(lia) Ptr (TablePackLiterals.machine_words _ _ _ _ _ K)
     (TablePackLiterals.enabled _ _ _ _ _ K) R Q).
 - intros x [Off NotRow];destruct(TablePacking.trace _ _ _ _ _ _ _ Q) as [ws [_ [_ [Safe Replay]]]].
   rewrite Replay,(WriteTrace.frame _ _ Safe _ _ NotRow),(TablePackLiterals.memory_after _ _ _ _ _ K),(TableTranspose.memory_after _ _ _ D),
     (TableStage.later _ _ _ _ _ _ C ltac:(lia)),M,(TableProduct.outside _ _ _ _ _ _ A).
   + reflexivity.
   + exact Off.
   + unfold TableCoordinates.frame;lia.
Qed.
