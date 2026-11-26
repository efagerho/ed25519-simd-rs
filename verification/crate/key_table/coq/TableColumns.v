From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.VectorProcedure memory.ByteMemory memory.FlatMemory.
From Ed25519Simd.KeyTable Require Image Fields.
From Ed25519Simd.KeyTable Require TableColumn TableTranspose.
From Ed25519Simd.KeyTable Require Import CallLayout.
Local Open Scope Z_scope.
Local Opaque TableColumn.value TableProduct.two_dt.

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

Definition index second i:=(if second:bool then 8+i else i)%nat.
Lemma reg_index b i : (i<8)%nat -> TableTranspose.reg b i=Image.reg_for (index b i).
Proof. intros N;destruct b;destruct i as [|[|[|[|[|[|[|[|i]]]]]]]];try lia;reflexivity. Qed.
