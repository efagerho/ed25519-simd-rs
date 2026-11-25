From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.WordBounds execution.VectorProcedure
 execution.ScalarBytes execution.QwordBlock execution.InstructionRoute execution.MappedFetch.
From Ed25519Simd.Decode Require HelperBytes DecoderBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require ScoreSetup NativeWords.
Local Open Scope Z_scope.
Local Notation pc:=(ScoreSetup.callee Dalek).
Local Notation text:=(ScoreSetup.code Dalek).
Module K:=DecoderKernel.
Definition start (y:bool):=if y then 341 else 501.
Definition seed:=skipn 5 (K.body K.Seed).
Definition code:=seed++(K.body K.Convolve++K.body K.Fold).
Definition body bias:=let h:=bias+Decode.HelperBytes.address in let raw:=Decode.HelperBytes.symbol_bytes in
 then_run (segment h raw (length seed))
   (then_run (wrapped h raw h raw (DecoderProduct.native bias K.Convolve)) (DecoderProduct.native bias K.Fold)).
Definition execute bias:=then_run (wrapped (bias+pc) text (bias+Decode.HelperBytes.address) Decode.HelperBytes.symbol_bytes (body bias))
 (wrapped (bias+pc) text (bias+Decode.DecoderBytes.address) Decode.DecoderBytes.symbol_bytes (DecoderProduct.native bias K.Carry)).
Lemma initial:linked Decode.HelperBytes.symbol_bytes (route 0xbae (map Arithmetic seed)).
Proof. apply checks_route;vm_compute;reflexivity. Qed.
Lemma seed_end:QwordBlock.after 0xbae (map Arithmetic seed)=0xbfc.
Proof. vm_compute;reflexivity. Qed.
Lemma columns bias e:placement e -> loaded Dalek bias (mem e) (writable e) ->
 contract e (writable e) (DecoderProduct.area e) (bias+Decode.HelperBytes.address+0xbae)
    (bias+Decode.HelperBytes.address+0xca3) 8 code (body bias).
Proof.
 intros P I;apply (compose _ _ _ _ (bias+Decode.HelperBytes.address+0xbfc) _ 0 8).
 - rewrite <-seed_end;apply VectorProcedure.block;[apply (DecoderProduct.placed Dalek bias e I K.Seed)|exact initial|vm_compute;reflexivity].
 - exact (DecoderProduct.after_seed _ _ _ P I).
Qed.

Theorem checked y bias e:placement e -> loaded Dalek bias (mem e) (writable e) ->
 contract e (writable e) (DecoderProduct.area e) (bias+pc+start y) (bias+pc+(start y+10)) 16
 (code++K.body K.Carry) (execute bias).
Proof.
 intros P I;set(o:=bias+pc);assert (Size:0<=start y /\ start y+10<Z.of_nat(length text)) by (destruct y;vm_compute;split;discriminate || reflexivity).
 assert (Scorer:available e (writable e) o text).
 { split;[exact (proj2(symbols _ _ _ _ I _ _ (ScoreSetup.image Dalek)))|intros x X;apply (immutable _ _ _ _ I);left;exists pc,text;auto using ScoreSetup.image]. }
 assert (Fits:forall i,0<=i<Z.of_nat(length text) -> word64(o+i))
    by (intros i X;destruct(proj1(symbols _ _ _ _ I _ _ (ScoreSetup.image Dalek)));unfold o,word64;lia).
 apply (compose _ _ _ _ (o+(start y+5)) _ 16 8).
 - apply (invoke _ _ _ o text (start y) ((Decode.HelperBytes.address+0xbae)-(pc+start y+5))
      (bias+Decode.HelperBytes.address) Decode.HelperBytes.symbol_bytes 0xca3 8).
   + apply DecoderProduct.stack,P.
   + lia.
   + exact Scorer.
   + exact (DecoderProduct.placed _ _ _ I K.Fold).
   + lia.
   + destruct y;vm_compute;reflexivity.
   + lia.
   + vm_compute;reflexivity.
   + replace (o+(start y+5)+(Decode.HelperBytes.address+0xbae-(pc+start y+5))) with (bias+Decode.HelperBytes.address+0xbae) by (unfold o;ring).
     exact (DecoderProduct.address_fits _ _ _ I K.Seed 0xbae ltac:(vm_compute;split;discriminate || reflexivity)).
   + apply Fits;lia.
   + replace (o+(start y+5)+(Decode.HelperBytes.address+0xbae-(pc+start y+5))) with (bias+Decode.HelperBytes.address+0xbae) by (unfold o;ring).
     exact (columns _ _ P I).
 - replace (start y+10) with ((start y+5)+5) by ring.
   apply (invoke _ _ _ o text (start y+5) ((Decode.DecoderBytes.address+0xa7e)-(pc+(start y+5)+5))
      (bias+Decode.DecoderBytes.address) Decode.DecoderBytes.symbol_bytes 0xadd 0).
   + apply DecoderProduct.stack,P.
   + lia.
   + exact Scorer.
   + exact (DecoderProduct.placed _ _ _ I K.Carry).
   + lia.
   + destruct y;vm_compute;reflexivity.
   + lia.
   + vm_compute;reflexivity.
   + replace (o+(start y+5+5)+(Decode.DecoderBytes.address+0xa7e-(pc+(start y+5)+5))) with (bias+Decode.DecoderBytes.address+0xa7e) by (unfold o;ring).
     exact (DecoderProduct.address_fits _ _ _ I K.Carry 0xa7e ltac:(vm_compute;split;discriminate || reflexivity)).
   + apply Fits;lia.
   + replace (o+(start y+5+5)+(Decode.DecoderBytes.address+0xa7e-(pc+(start y+5)+5))) with (bias+Decode.DecoderBytes.address+0xa7e) by (unfold o;ring).
     exact (DecoderProduct.calc _ _ _ I K.Carry).
Qed.

Lemma wf bias:NativeWords.words(execute bias).
Proof. unfold execute,body,DecoderProduct.native;repeat first [apply NativeWords.sequence|apply NativeWords.call|apply NativeWords.block]. Qed.
