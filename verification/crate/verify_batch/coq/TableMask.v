From Coq Require Import ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.MaskTransfer.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require EligibleLanes TablePackedInputs TablePackLiterals.
Local Open Scope Z_scope.

Definition masks t:=FinishTrace.masks (PairReturn.signature (DecoderReturn.points(EligibleLanes.decoded t))).
Definition execute bias p bank:=bind (TablePackedInputs.execute bias p) (fun q=>TablePackLiterals.execute bias q bank).
Record ready pol bias e p q bank:Prop:=Ready {
 address:ip q=TableFrame.base bias+1207;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 pointers:TableMultiple.pointers pol e 1 (machine q);
 packed:forall b j i,(j<8)%nat -> (i<8)%nat -> vectors(machine q) i (TableTranspose.reg b j)=
  TablePackedInputs.column e (machine p) j (TablePackedInputs.index b i);
 tail:forall j i,(j<8)%nat -> (i<4)%nat -> vectors(machine q) j (1+i)%nat=TablePackedInputs.column e (machine p) j (16+i)%nat;
 literals:forall i j,(i<3)%nat -> (j<8)%nat -> vectors(machine q) j (28+i)%nat=List.nth j (TablePackLiterals.words i) 0;
 enabled:forall j,(j<8)%nat -> bank 1%nat j=Z.testbit Pack.mask (Z.of_nat j);
 staged:forall j i,(j<8)%nat -> (i<15)%nat -> ByteMemory.read_word (mem(machine q))
  (TableProduct.frame pol e+64*Z.of_nat i+8*Z.of_nat j)=TablePackedInputs.column e (machine p) j i;
 parent:TableParentFrame.retained pol bias e (machine p) (machine q);
 point_after:preserved (span (TableEntry.point e) 1280) (mem(machine p)) (mem(machine q));
 center:forall j i,(j<8)%nat -> 0<=i<20 ->
  ByteMemory.read_word (mem(machine q)) (TableIdentity.center (TableIdentity.first e) j+8*i)=KeyTable.Image.identity_word i
}.
Lemma aligned bias : (bias+DecoderFrame.origin) mod 64=0 -> TableFrame.base bias mod 64=0.
Proof.
 intro H;rewrite Z.add_mod in H by lia;unfold TableFrame.base;rewrite Z.add_mod by lia.
 change (DecoderFrame.origin mod 64) with 0 in H;change (TableEntry.origin mod 64) with 0;exact H.
Qed.
Theorem checked pol bias e before p ks : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> EligibleLanes.post pol bias e before p -> regs(machine p) 14%nat<>0 ->
 exists q bank,execute bias p ks=Some(q,bank) /\ ready pol bias e p q bank.
Proof.
 intros P I Align E Live;destruct(TablePackedInputs.checked _ _ _ _ _ P I E Live) as [a [Run A]].
 destruct(TablePackLiterals.checked pol bias e a ks I (aligned _ Align) (TablePackedInputs.address _ _ _ _ _ A)
   (TablePackedInputs.writes _ _ _ _ _ A) (TablePackedInputs.words _ _ _ _ _ A)) as [q [bank [Loaded L]]].
 exists q,bank;split;[unfold execute;rewrite Run;exact Loaded|constructor].
 - exact (TablePackLiterals.address _ _ _ _ _ L).
 - exact (TablePackLiterals.writes _ _ _ _ _ L).
 - exact (TablePackLiterals.machine_words _ _ _ _ _ L).
 - destruct(TablePackedInputs.arguments _ _ _ _ _ A);constructor;rewrite (TablePackLiterals.registers _ _ _ _ _ L);assumption.
 - intros b j i J N;rewrite (TablePackLiterals.prior _ _ _ _ _ L);[apply (TablePackedInputs.pair _ _ _ _ _ A);assumption|].
   destruct b;destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];try lia;vm_compute;lia.
 - intros j i J N;rewrite (TablePackLiterals.prior _ _ _ _ _ L) by lia;apply (TablePackedInputs.tail _ _ _ _ _ A);assumption.
 - exact (TablePackLiterals.literals _ _ _ _ _ L).
 - exact (TablePackLiterals.enabled _ _ _ _ _ L).
 - intros j i J N;rewrite (TablePackLiterals.memory_after _ _ _ _ _ L);apply (TablePackedInputs.staged _ _ _ _ _ A);assumption.
 - unfold TableParentFrame.retained;rewrite (TablePackLiterals.memory_after _ _ _ _ _ L);exact (TablePackedInputs.parent _ _ _ _ _ A).
 - rewrite (TablePackLiterals.memory_after _ _ _ _ _ L);apply (TablePackedInputs.point_after _ _ _ _ _ A).
 - rewrite (TablePackLiterals.memory_after _ _ _ _ _ L);apply (TablePackedInputs.rows _ _ _ _ _ A).
Qed.
