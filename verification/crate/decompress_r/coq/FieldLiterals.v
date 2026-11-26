From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordSemantics execution.WordBounds execution.MappedFetch
 memory.ByteMemory memory.FlatMemory memory.MemoryGeometry.
From Ed25519Simd.Decode Require HelperBytes.
Import ListNotations. Local Open Scope Z_scope.

Definition constant (i:nat) := nth i [19;2^51-1;(2^51-19)*1024;(2^51-1)*1024] 0.
Definition field_offset i := 0xde0+8*Z.of_nat i.
Lemma offsets i : (i<4)%nat -> 0<=field_offset i /\ field_offset i+8<=Z.of_nat(length HelperBytes.symbol_bytes).
Proof. intros I;unfold field_offset;change (Z.of_nat(length HelperBytes.symbol_bytes)) with 3656;lia. Qed.
Lemma literal_value i : (i<4)%nat ->
 read_word (fun x=>nth (Z.to_nat x) HelperBytes.symbol_bytes 0) (field_offset i)=constant i.
Proof. intros I;destruct i as [|[|[|[|i]]]];[vm_compute;reflexivity..|lia]. Qed.
Lemma literal_read m base bs n : mapped m base bs -> forall off,0<=off ->
 off+Z.of_nat n<=Z.of_nat(length bs) ->
 read_le n m (base+off)=read_le n (fun x=>nth (Z.to_nat x) bs 0) off.
Proof.
 intros M;induction n as [|n IH];intros off L H;[reflexivity|].
 cbn [read_le];replace (base+off+1) with (base+(off+1)) by ring;rewrite IH by lia.
 rewrite <- (M (Z.to_nat off)) by lia;now rewrite Z2Nat.id by lia.
Qed.
Lemma read_literal bias a bs off value m : mapped m (bias+a) bs -> fits64 (bias+a) (Z.of_nat(length bs)) ->
 0<=off -> off+8<=Z.of_nat(length bs) -> read_word (fun x=>nth (Z.to_nat x) bs 0) off=value ->
 read_word m (word(bias+a+off))=value.
Proof.
 intros Map [L H] Pos Ext Value;rewrite word_fits by (unfold word64;lia).
 unfold read_word;rewrite (literal_read _ _ _ 8 Map off Pos Ext);exact Value.
Qed.
