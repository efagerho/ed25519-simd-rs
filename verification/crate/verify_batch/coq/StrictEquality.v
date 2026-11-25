From Coq Require Import ZArith Bool Lia.
From Coqprime.elliptic Require GZnZ.
From Machine Require Import execution.LinkedCalls memory.ByteMemory.
From Curve25519 Require Import Field.
From Curve25519.group Require Import PrimeField Affine Cofactor Representation Decompression.
From Ed25519Simd.Dalek Require Encoding.
From Ed25519Simd.VerifyBatch Require Import Policy Return.
From Ed25519Simd.VerifyBatch Require StrictAccept ScorePoint.
Local Open Scope Z_scope.

(* Once the canonical-Y and small-order screens have passed, equality of the
   two affine coordinates is exactly the strict encoded-signature test. *)
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Lemma canonical_bytes e j R:byte_memory(mem e) ->
 decodes (BatchDecode.original_encoding true e j) R ->
 BatchDecode.original_encoding true e j mod 2^255<prime -> multiple 8 R<>identity ->
 BatchDecode.original_encoding true e j=compression R.
Proof.
 intros B [Y Sign] Canon Strong;set(w:=BatchDecode.original_encoding true e j) in *.
 set(ptr:=descriptor (mem e) (regs e 7%nat) (BatchWindow.row e j) 8).
 assert (Raw:w=Decode.Unpack.encoded (mem e) ptr 0%nat).
 { unfold w,BatchDecode.original_encoding,read_input,ptr;cbn [r_bytes];rewrite Digest.read_octets by exact B.
   unfold Decode.Unpack.encoded;now rewrite Z.add_0_r. }
 change (w=Dalek.Encoding.compress R);rewrite Raw;apply (proj2(Dalek.Encoding.encoding_equal _ _ _ _ B));rewrite <-Raw.
 split.
 - rewrite Y;change (w mod 2^255=(w mod 2^255) mod prime).
   rewrite (Z.mod_small _ prime);[reflexivity|pose proof(Z.mod_pos_bound w (2^255) ltac:(lia));lia].
 - destruct Sign as [X|Parity];[exfalso;apply Strong,eight_identity_iff;rewrite X;ring|symmetry;exact Parity].
Qed.

Theorem coordinates e j A R:byte_memory(mem e) -> StrictOrderClear.eligible e j ->
 decodes (little_endian(key_bytes(HashLayout.row e j))) A ->
 decodes (BatchDecode.original_encoding true e j) R ->
 (x(ScorePoint.product e j A)=x R /\ y(ScorePoint.product e j A)=y R <->
  signature_accepts Dalek (HashLayout.row e j)).
Proof.
 intros B [[On Canon] [R' [DR' Strong]]] DA DR.
 destruct On as [S [Dec [A' [DA' Key]]]];rewrite (Lane.unique_key _ _ _ DA' DA) in Key.
 rewrite (Lane.unique_key _ _ _ DR' DR) in Strong.
 set(Q:=ScorePoint.product e j A).
 split.
 - intro Eq;apply point_ext in Eq;split;[exact S|exists A;split;[exact DA|split;[apply Key;reflexivity|]]].
   change (BatchDecode.original_encoding true e j=compression Q /\ multiple 8 Q<>identity);rewrite Eq;split;
     [exact (canonical_bytes _ _ _ B DR Canon Strong)|exact Strong].
 - intros [_ [a [DA0 [_ [E _]]]]];rewrite (Lane.unique_key _ _ _ DA0 DA) in E.
   change (BatchDecode.original_encoding true e j=compression Q) in E;rewrite E in DR.
   rewrite (Lane.unique_key _ _ _ DR (Lane.decodes_compression Q));auto.
Qed.
End Iteration.
