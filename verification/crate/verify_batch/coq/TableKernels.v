From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.VectorProcedure
 execution.WordBounds memory.MemoryGeometry.
From Ed25519Simd.Decode Require Kernels Program DecoderBytes.
From Ed25519Simd.KeyTable Require Fields.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require TableEntry TableFrame BatchDecode DecoderKernel DecoderProduct NativeWords.
Local Open Scope Z_scope.

(* All four field columns return through the same RET in the decoder image.
   TwoDT also calls the shared convolution before reaching that carry code. *)
Definition site op:=match op with Fields.TwoDT=>254 | Fields.YMinusX=>398 | Fields.YPlusX=>512 | Fields.TwoZ=>617 end.
Definition target op:=match op with Fields.TwoDT=>0xa79 | _=>0xa7e end.
Definition depth op:=match op with Fields.TwoDT=>16 | _=>0 end.
Definition code op:=match op with Fields.TwoDT=>Kernels.product | _=>Kernels.carry end Ed25519Simd.Decode.Program.code.
Definition body bias op:=match op with Fields.TwoDT=>DecoderProduct.product bias | _=>DecoderProduct.native bias DecoderKernel.Carry end.
Definition call bias op:=wrapped (TableFrame.base bias) TableFrame.text (bias+DecoderBytes.address) DecoderBytes.symbol_bytes (body bias op).
Definition disp op:=DecoderBytes.address+target op-(TableEntry.origin+(site op+5)).
Lemma sites op : ScalarBytes.decode (skipn (Z.to_nat(site op)) TableFrame.text)=Some(5%nat,CallRelative(disp op)).
Proof. destruct op;vm_compute;reflexivity. Qed.

Theorem checked pol bias e op : placement e -> loaded pol bias (mem e) (writable e) ->
 contract e (writable e) (DecoderProduct.area e) (TableFrame.base bias+site op) (TableFrame.base bias+(site op+5))
   (8+depth op) (code op) (call bias op).
Proof.
 intros P I;unfold call.
 eapply (invoke _ _ _ _ _ _ (disp op) _ _ 0xadd).
 - exact (DecoderProduct.stack e P).
 - destruct op;cbn [depth];lia.
 - destruct(symbols _ _ _ _ I _ _ (TableEntry.image pol)) as [_ Code];split;[exact Code|].
   intros x X;apply (immutable _ _ _ _ I);left;exists TableEntry.origin,TableFrame.text;split;[apply TableEntry.image|exact X].
 - exact (DecoderProduct.placed pol bias e I DecoderKernel.Carry).
 - destruct op;cbn [site];lia.
 - apply sites.
 - lia.
 - vm_compute;reflexivity.
 - replace (TableFrame.base bias+(site op+5)+disp op) with (bias+DecoderBytes.address+target op) by
    (unfold TableFrame.base,disp;ring).
   apply (DecoderProduct.address_fits pol bias e I DecoderKernel.Carry);change (0<=target op<2984);destruct op;cbn [target];lia.
 - destruct(proj1(symbols _ _ _ _ I _ _ (TableEntry.image pol))) as [L H].
   change (Z.of_nat(length TableFrame.text)) with 2280 in H.
   change (0<=bias+TableEntry.origin) in L;change (bias+TableEntry.origin+2280<=2^64) in H.
   unfold TableFrame.base,word64;destruct op;cbn [site];lia.
 - replace (TableFrame.base bias+(site op+5)+disp op) with (bias+DecoderBytes.address+target op) by
    (unfold TableFrame.base,disp;ring).
   destruct op;[exact (DecoderProduct.check_product pol bias e P I)| | |];
    exact (DecoderProduct.calc pol bias e I DecoderKernel.Carry).
Qed.

Lemma preserves_words bias op : NativeWords.words(call bias op).
Proof.
 apply NativeWords.call;destruct op;unfold body,DecoderProduct.product,DecoderProduct.columns,DecoderProduct.native;
 repeat first [apply NativeWords.sequence|apply NativeWords.call|apply NativeWords.block].
Qed.
