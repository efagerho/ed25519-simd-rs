From Coq Require Import ZArith List Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.VectorProcedure memory.FlatMemory memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.KeyTable Require Image Fields.
From Ed25519Simd.KeyTable Require TableSignedWords TableNextDigit TableAdd TableColumns TableCoordinates TableStage.
From Ed25519Simd.KeyTable Require Import CallLayout.
Local Open Scope Z_scope.

Definition execute bias p ks:=bind (TableProduct.execute bias p) (fun a=>
 bind (TableCoordinates.start bias a) (fun b=>bind (TableStage.execute bias b) (fun c=>
 bind (TableTranspose.execute bias c) (fun d=>bind (TablePackLiterals.execute bias d ks)
 (fun '(mask,bank)=>TablePacking.execute bias mask bank))))).
Definition preserved_byte e digit x:=
 ~(CallLayout.stage e-24<=x<CallLayout.stage e) /\ ~TablePackRows.area e digit x /\
 (digit=1 -> ~TableStage.buffer (CallLayout.stage e) x).
Lemma stack_outside e d x : placement e -> 1<=d<=8 -> span (CallLayout.stage e) 960 x -> ~TablePackRows.area e d x.
Proof. intros P D X Hit;apply (TablePackRows.in_table _ _ _ D) in Hit;pose proof(CallLayout.depth e P);
 pose proof(table_stack _ P);unfold span,disjoint in *;lia. Qed.
Record post (root:cpu) bias e digit p q:Prop:=Post {
 address:ip q=CallLayout.base bias+1947;
 writes:accounted root (writable e) q;
 words:well_formed(machine q);
 pointers:TableMultiple.pointers e digit (machine q);
 rows:TableSignedWords.signed e digit (TableColumns.column e (machine p)) (machine q);
 first_staged:digit=1 -> forall i j,(i<15)%nat -> (j<8)%nat ->
   read_word (mem(machine q)) (CallLayout.stage e+64*Z.of_nat i+8*Z.of_nat j)=
   TableColumns.column e (machine p) j i;
 outside:preserved (preserved_byte e digit) (mem(machine p)) (mem(machine q))
}.
Lemma elsewhere e s t : placement e ->
 preserved (fun x=>~(CallLayout.stage e-24<=x<CallLayout.stage e)) (mem s) (mem t) ->
 preserved (span (CallLayout.point_ptr e) 1280) (mem s) (mem t).
Proof.
 intros P M x X;apply M;pose proof(CallLayout.point_stack _ P) as Apart;pose proof(CallLayout.depth e P) as Depth;
 unfold span,disjoint in *;lia.
Qed.
Theorem checked (root:cpu) bias e digit before p ks : placement e -> loaded root bias e ->
 (bias+DecoderBytes.address) mod 64=0 -> 1<=digit<=8 -> TableMultiple.positioned root bias e digit before p ->
 exists q bank,execute bias p ks=Some(q,bank) /\ post root bias e digit p q.
Proof.
 intros P I Al N Init;destruct(TableProduct.checked _ _ _ _ _ _ P I Init) as [a [Product A]].
 destruct(TableCoordinates.checked _ _ _ _ _ P I (TableProduct.address _ _ _ _ _ _ A) (TableProduct.writes _ _ _ _ _ _ A)
  (TableProduct.words _ _ _ _ _ _ A) (TableProduct.arguments _ _ _ _ _ _ A) (TableProduct.constants _ _ _ _ _ _ A))
  as [b [Fields [PC [Acc [W [G [M Col]]]]]]].
 assert (PB:TableMultiple.pointers e digit (machine b)) by (destruct(TableProduct.arguments _ _ _ _ _ _ A);constructor;now rewrite G).
 assert (Values:forall j i,(j<8)%nat -> (i<20)%nat ->
  vectors(machine b) j (Image.reg_for i)=TableColumns.column e (machine p) j i).
 { apply TableColumns.from_fields;intros j i J L;split.
   - rewrite (TableCoordinates.product _ _ _ Col j i L);exact (TableProduct.limbs _ _ _ _ _ _ A j i L).
   - pose proof(elsewhere e _ _ P (TableProduct.outside _ _ _ _ _ _ A)) as Point;repeat split.
     + rewrite (TableCoordinates.difference _ _ _ Col j i J L);now apply TableCoordinates.point_value.
     + rewrite (TableCoordinates.sum _ _ _ Col j i J L);now apply TableCoordinates.point_value.
     + rewrite (TableCoordinates.twice _ _ _ Col j i J L);now apply TableCoordinates.point_value. }
 destruct(TableStage.checked _ _ _ digit b P I ltac:(lia) PC Acc W (TableMultiple.multiple _ _ _ PB) (TableMultiple.count _ _ _ PB)
    (TableMultiple.stack _ _ _ PB)) as [c [Stage C]].
 destruct(TableTranspose.checked root bias e c I (TableStage.address _ _ _ _ _ _ C) (TableStage.writes _ _ _ _ _ _ C)
   (TableStage.words _ _ _ _ _ _ C)) as [d [Trans [DPC D]]].
 destruct(TablePackLiterals.checked root bias e d ks I (TablePackLiterals.aligned _ Al) DPC (TableTranspose.writes _ _ _ _ D) (TableTranspose.words _ _ _ _ D))
   as [m [bank [Mask K]]].
 assert (Ptr:TableMultiple.pointers e digit (machine m)).
 { destruct PB;constructor;rewrite (TablePackLiterals.registers _ _ _ _ _ _ K);cbn [Instructions.put Nat.eqb];
   rewrite (TableTranspose.registers _ _ _ _ D),(TableStage.registers _ _ _ _ _ _ C);assumption. }
 destruct(TablePacking.checked root bias e digit m bank P I ltac:(lia) (TablePackLiterals.address _ _ _ _ _ _ K) (TablePackLiterals.writes _ _ _ _ _ _ K)
   (TablePackLiterals.machine_words _ _ _ _ _ _ K) Ptr) as [q [Pack Q]].
 exists q,bank;split;[unfold execute;rewrite Product;cbn [bind];rewrite Fields;cbn [bind];rewrite Stage;cbn [bind];rewrite Trans;cbn [bind];rewrite Mask;exact Pack|constructor].
 - exact (TablePacking.address _ _ _ _ _ _ _ Q).
 - exact (TablePacking.writes _ _ _ _ _ _ _ Q).
 - exact (TablePacking.words _ _ _ _ _ _ _ Q).
 - exact (TablePacking.arguments _ _ _ _ _ _ _ Q).
 - assert (R:TablePackValues.represents (TableColumns.column e (machine p)) TablePackValues.initial (machine m)).
   { apply TablePackValues.from_registers.
     - intros side j i J L;rewrite (TablePackLiterals.prior _ _ _ _ _ _ K).
       2:{ destruct side;destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];try lia;vm_compute;lia. }
       rewrite (TableTranspose.rows _ _ _ _ D side j i J L),(TableStage.bank _ _ _ _ _ _ C),TableColumns.reg_index by exact L.
       apply Values;[exact J|destruct side;cbn [TableColumns.index];lia].
     - intros j i J L;rewrite (TablePackLiterals.prior _ _ _ _ _ _ K) by lia;rewrite (TableTranspose.tail_rows _ _ _ _ D i j L J),(TableStage.bank _ _ _ _ _ _ C).
       replace (1+i)%nat with (Image.reg_for (16+i)) by (destruct i as [|[|[|[|i]]]];try lia;reflexivity);apply Values;lia.
     - exact (TablePackLiterals.literals _ _ _ _ _ _ K). }
   exact (TableSignedWords.contents root bias e digit m q bank _ P ltac:(lia) Ptr (TablePackLiterals.machine_words _ _ _ _ _ _ K)
     (TablePackLiterals.enabled _ _ _ _ _ _ K) R Q).
 - intros First i j Ibound J.
   rewrite <-(Values j i J ltac:(lia)).
   rewrite <-(TableStage.positive _ _ _ _ _ _ C First i j Ibound J).
   rewrite <-(TableTranspose.memory_after _ _ _ _ D),<-(TablePackLiterals.memory_after _ _ _ _ _ _ K).
   apply preserved_read with (outside:=fun x=>~TablePackRows.area e digit x).
   + intros x X;destruct(TablePacking.trace _ _ _ _ _ _ _ Q) as [ws [_ [_ [Safe Replay]]]].
     rewrite Replay;apply (WriteTrace.frame _ _ Safe),X.
   + intros k Range;apply (stack_outside e digit _ P N);unfold CallLayout.stage,span.
     change (0<=k<8) in Range;lia.
 - intros x [Off [NotRow StageOff]];destruct(TablePacking.trace _ _ _ _ _ _ _ Q) as [ws [_ [_ [Safe Replay]]]].
   assert (S:mem(machine c) x=mem(machine b) x).
   { destruct (Z.eq_dec digit 1) as [First|Later].
     - apply (TableStage.outside _ _ _ _ _ _ C x (StageOff First)).
     - now rewrite (TableStage.later _ _ _ _ _ _ C Later). }
   rewrite Replay,(WriteTrace.frame _ _ Safe _ _ NotRow),(TablePackLiterals.memory_after _ _ _ _ _ _ K),(TableTranspose.memory_after _ _ _ _ D),
     S,M,(TableProduct.outside _ _ _ _ _ _ A).
   + reflexivity.
   + exact Off.
   + unfold TableCoordinates.frame;lia.
Qed.
