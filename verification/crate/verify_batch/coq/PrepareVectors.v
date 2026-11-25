From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.MappedFetch execution.MaskTransfer execution.MaskedResult memory.ByteMemory memory.FlatMemory.
From Ed25519Simd.PrepareChunk Require Caller CommonBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require DecoderFrame.
Import ListNotations. Local Open Scope Z_scope.

Definition text:=CommonBytes.symbol_bytes.
Definition origin bias:=bias+PrepareNative.common.
Definition pointers:=[BroadcastGpr 0 3; WidenWords 1 274; BroadcastGpr 2 12; FromGpr 1 15; AddQ 2 1 0 1].
Definition flags:=[FromGpr 1 14;MaskBytes 0 1;AbsBytes 0 0].
Definition fragment off len:=firstn len (skipn off text).

Lemma pointer_code:assemble 185 pointers=Some(fragment 185 33).
Proof. vm_compute;reflexivity. Qed.
Lemma flag_code:assemble 225 flags=Some(fragment 225 17).
Proof. vm_compute;reflexivity. Qed.
Lemma literal j : (j<8)%nat -> read_le 2 (fun x=>nth (Z.to_nat x) text 0) (274+2*Z.of_nat j)=Caller.table_offset j.
Proof. intros J;destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];try lia;reflexivity. Qed.

Definition unchanged e:=MaskedResult.unchanged e (writable e).
Lemma block pol bias e p ks off n ops v k :
 loaded pol bias (mem e) (writable e) -> ip p=origin bias+Z.of_nat off ->
 accounted e (writable e) p -> well_formed(machine p) -> (off+n<length text)%nat ->
 assemble (Z.of_nat off) ops=Some(fragment off n) ->
 evaluate (origin bias) (machine p) ks ops=Some(v,k) ->
 exists q,MaskedResult.execute (origin bias) ops p ks=Some(q,k) /\
 ip q=origin bias+Z.of_nat(off+n) /\ machine q=v /\ unchanged e p q.
Proof.
 intros I PC Acc W N Enc Eval.
 destruct(proj1(symbols _ _ _ _ I _ _ (in_common pol))) as [L H].
 exact (mapped_slice _ text e (writable e) _ _ _ _ _ _ _ L H (proj1(mapped_now _ _ _ I _ _ _ Acc (in_common pol))) PC Acc W N Enc Eval).
Qed.

Definition bank_from s ks r:=set_mask ks 1 16 (fun j=>Z.testbit (regs s r) (Z.of_nat j)).
Lemma mask_bit s ks r j : (j<8)%nat -> bank_from s ks r 1%nat j=Z.testbit (regs s r) (Z.of_nat j).
Proof. intro J;unfold bank_from,set_mask,put;cbn [Nat.eqb];now rewrite (proj2(Nat.ltb_lt j 16) ltac:(lia)). Qed.

Theorem pointer_values pol bias e p ks : placement e -> loaded pol bias (mem e) (writable e) ->
 ip p=origin bias+185 -> accounted e (writable e) p -> well_formed(machine p) -> regs(machine p) 3%nat=scratch e ->
 exists q bank,MaskedResult.execute (origin bias) pointers p ks=Some(q,bank) /\ ip q=origin bias+218 /\ unchanged e p q /\
 forall j,(j<8)%nat -> vectors(machine q) j 2%nat=
 if Z.testbit (regs(machine p) 15%nat) (Z.of_nat j) then scratch e+Caller.table_offset j else regs(machine p) 12%nat.
Proof.
 intros P I PC Acc W BX;set (s:=machine p) in *;set (o:=origin bias) in *.
 set (offsets:=fun j=>read_le 2 (mem s) (word(o+274)+2*Z.of_nat j)).
 set (v:=vector_dest (vector_dest (vector_dest s 0 (fun _=>regs s 3%nat)) 1 offsets) 2 (fun _=>regs s 12%nat)).
 set (k:=bank_from s ks 15).
 set (t:=merge v k 2 1 (fun j=>Arithmetic.vpaddq (vectors v j 0%nat) (vectors v j 1%nat))).
 assert (E:evaluate o s ks pointers=Some(t,k)) by reflexivity.
 destruct(block pol bias e p ks 185 33 pointers t k I PC Acc W ltac:(change (218<290)%nat;lia) pointer_code E)
   as [q [Run [End [CPU U]]]].
 exists q,k;split;[exact Run|split;[exact End|split;[exact U|]]];intros j J;rewrite CPU.
 change ((if k 1%nat j then Arithmetic.vpaddq (regs s 3%nat) (offsets j) else regs s 12%nat)=(if Z.testbit (regs s 15%nat) (Z.of_nat j) then scratch e+Caller.table_offset j else regs s 12%nat)).
 unfold k;rewrite mask_bit by exact J;destruct(Z.testbit _ _);[|reflexivity].
 destruct(mapped_now _ _ _ I _ _ _ Acc (in_common pol)) as [Map Sep].
 destruct(proj1(symbols _ _ _ _ I _ _ (in_common pol))) as [L H];change (o+290<=2^64) in H;change (0<=o) in L.
 unfold offsets;rewrite word_fits by (unfold word64;lia).
 replace (o+274+2*Z.of_nat j) with (o+(274+2*Z.of_nat j)) by ring.
 rewrite (DecoderFrame.literal_read _ _ text 2 Map) by (change (Z.of_nat(length text)) with 290;lia).
 rewrite literal,BX by exact J;apply low64_id.
 destruct(scratch_ok _ P) as [[A B] _];unfold Caller.table_offset,Caller.tables_offset,Caller.table_stride,word64;lia.
Qed.

Theorem flag_values pol bias e p ks : loaded pol bias (mem e) (writable e) -> ip p=origin bias+225 ->
 accounted e (writable e) p -> well_formed(machine p) ->
 exists q bank,MaskedResult.execute (origin bias) flags p ks=Some(q,bank) /\ ip q=origin bias+242 /\ unchanged e p q /\
 forall j,(j<8)%nat -> word_byte (vectors(machine q) 0%nat 0%nat) (Z.of_nat j)=Z.b2z (Z.testbit (regs(machine p) 14%nat) (Z.of_nat j)).
Proof.
 intros I PC Acc W;set (s:=machine p);set (k:=bank_from s ks 14).
 set (v:=vector_dest s 0 (mask_qword (k 1%nat))).
 set (t:=vector_dest v 0 (fun j=>abs_qword (vectors v j 0%nat))).
 assert (E:evaluate (origin bias) s ks flags=Some(t,k)) by reflexivity.
 destruct(block pol bias e p ks 225 17 flags t k I PC Acc W ltac:(change (242<290)%nat;lia) flag_code E)
   as [q [Run [End [CPU U]]]].
 exists q,k;split;[exact Run|split;[exact End|split;[exact U|]]];intros j J;rewrite CPU.
 change (word_byte (abs_qword (mask_qword (k 1%nat) 0)) (Z.of_nat j)=Z.b2z(Z.testbit (regs s 14%nat) (Z.of_nat j))).
 rewrite abs_mask_byte by exact J;change (Z.b2z (bank_from s ks 14 1%nat j)=Z.b2z(Z.testbit (regs s 14%nat) (Z.of_nat j)));now rewrite mask_bit.
Qed.
