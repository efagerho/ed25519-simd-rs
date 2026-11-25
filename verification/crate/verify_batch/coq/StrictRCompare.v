From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 execution.MappedFetch execution.PredicateBlock memory.ByteMemory.
From Machine Require execution.MaskedWords execution.MaskTransfer.
From Curve25519 Require Import Radix51.
From Ed25519Simd.Dalek Require Encoding.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require StrictRY.
Import ListNotations. Local Open Scope Z_scope.
Local Notation pc:=(ScoreSetup.callee Dalek).
Local Notation text:=(ScoreSetup.code Dalek).
Definition low_word:=DecoderFrame.origin+0xb88-pc.
Definition compare_low:=MaskedWords.Compare MaskedWords.AtLeastU 2 1 0 (MaskedWords.Rip low_word).
Definition ops:=[RootMasks.mask1;compare_low].
Definition fragment:=firstn 17 (skipn 130 text).
Lemma image:MaskedWords.assemble 130 ops=Some fragment /\ length fragment=17%nat.
Proof. vm_compute;split;reflexivity. Qed.
Definition execute bias:=PredicateBlock.execute (bias+pc) ops.
Definition bank o s ks:=update o s (RootMasks.gate o s ks) 2 compare_low.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record result bias e p q ks:Prop:=Result {
 at_kmov:ip q=bias+pc+147; writes:accounted e (writable e) q;
 machine_after:machine q=machine p; history:log q=log p;
 noncanonical:forall j,(j<8)%nat -> (ks 2%nat j=false <->
  BatchDecode.original_encoding true e j mod 2^255<Field.prime);
 upper:forall j,(8<=j)%nat -> ks 2%nat j=false
}.

Theorem checked bias e start p ks : loaded Dalek bias (mem e) (writable e) -> StrictRY.loaded_y bias e start p ->
 exists q k,execute bias p ks=Some(q,k) /\ result bias e p q k.
Proof.
 intros I Y;set (o:=bias+pc);set (s:=machine p);pose proof(StrictRY.writes _ _ _ _ Y) as Prev.
 pose proof(StrictRY.at_compare _ _ _ _ Y) as PC;fold o in PC.
 destruct(mapped_now _ _ _ I _ _ _ Prev (ScoreSetup.image Dalek)) as [Map _].
 destruct(proj1(symbols _ _ _ _ I _ _ (ScoreSetup.image Dalek))) as [L H];fold o in L,H;change (o+584<=2^64) in H.
 assert (Bytes:mapped (mem s) (ip p) fragment).
 { rewrite PC;apply MaskTransfer.subimage with (text:=text) (off:=130%nat);[exact Map|change (130+17<=584)%nat;lia|reflexivity]. }
 set (k:=bank o s ks).
 pose proof(PredicateBlock.mapped_block o 130 ops p ks fragment k PC (proj1 image) Bytes eq_refl) as R.
 assert (Next:word(ip p+Z.of_nat(length fragment))=o+147).
 { rewrite PC,(proj2 image);apply word_fits || (replace (o+130+Z.of_nat 17) with (o+147) by ring;apply word_fits);unfold word64;lia. }
 assert (Literal:read_word (mem s) (word(o+low_word))=radix-19).
 { replace (o+low_word) with (bias+DecoderFrame.origin+0xb88) by (unfold o,low_word;ring).
   eapply NativeScale.read_literal;[exact (proj1(mapped_now _ _ _ I _ _ _ Prev (BatchDecode.decode_in Dalek)))|
    exact (proj1(symbols _ _ _ _ I _ _ (BatchDecode.decode_in Dalek)))|lia|change (0xb88+8<=2984);lia|vm_compute;reflexivity]. }
 do 2 eexists;split;[exact R|constructor];try reflexivity;try exact Prev;try exact Next.
 - intros j J;unfold k,bank,compare_low;rewrite PredicateBlock.compare;cbn [MaskedWords.holds PredicateBlock.operand Nat.eqb orb].
   unfold RootMasks.gate,RootMasks.mask1;rewrite PredicateBlock.compare;cbn [MaskedWords.holds PredicateBlock.operand Nat.eqb orb].
   rewrite (proj2(Nat.ltb_lt j 8) J);cbn [andb].
   rewrite Literal;unfold s;rewrite (StrictRY.high _ _ _ _ Y j J),(StrictRY.mask _ _ _ _ Y j),(StrictRY.low _ _ _ _ Y j J).
   exact (StrictRY.canonical _ _ _ _ Y j J).
 - intros j J;unfold k,bank,compare_low;rewrite PredicateBlock.compare,(proj2(Nat.ltb_ge j 8) J);reflexivity.
Qed.
End Iteration.
