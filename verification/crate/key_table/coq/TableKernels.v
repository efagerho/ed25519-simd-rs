From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.VectorProcedure
 execution.WordBounds memory.MemoryGeometry.
From Ed25519Simd.Decode Require Kernels Program DecoderBytes.
From Ed25519Simd.KeyTable Require Fields.
From Ed25519Simd.KeyTable Require Import CallLayout.
From Ed25519Simd.Decode Require NativeProduct DecoderKernel.
From Machine Require execution.ProcedureWords.
Local Open Scope Z_scope.

(* All four field columns return through the same RET in the decoder image.
   TwoDT also calls the shared convolution before reaching that carry code. *)
Definition site op:=match op with Fields.TwoDT=>254 | Fields.YMinusX=>398 | Fields.YPlusX=>512 | Fields.TwoZ=>617 end.
Definition target op:=match op with Fields.TwoDT=>0xa79 | _=>0xa7e end.
Definition depth op:=match op with Fields.TwoDT=>16 | _=>0 end.
Definition code op:=match op with Fields.TwoDT=>Kernels.product | _=>Kernels.carry end Ed25519Simd.Decode.Program.code.
Definition body bias op:=match op with Fields.TwoDT=>NativeProduct.product bias | _=>NativeProduct.native bias DecoderKernel.Carry end.
Definition call bias op:=wrapped (CallLayout.base bias) CallLayout.text (bias+DecoderBytes.address) DecoderBytes.symbol_bytes (body bias op).
Definition disp op:=DecoderBytes.address+target op-(CallLayout.origin+(site op+5)).
Lemma sites op : ScalarBytes.decode (skipn (Z.to_nat(site op)) CallLayout.text)=Some(5%nat,CallRelative(disp op)).
Proof. destruct op;vm_compute;reflexivity. Qed.

Lemma member b:In(NativeProduct.section b,DecoderKernel.image b) children.
Proof. destruct b;apply helper_in || apply decoder_in. Qed.
Lemma placed root bias e : loaded root bias e -> forall b,available root (writable e) (bias+NativeProduct.section b) (DecoderKernel.image b).
Proof. intros I b;exact (proj2(symbols _ _ _ I _ _ (member b))). Qed.
Lemma fits root bias e : loaded root bias e -> forall b off,0<=off<Z.of_nat(length(DecoderKernel.image b)) ->
 word64(bias+NativeProduct.section b+off).
Proof. intros I b off B;destruct(proj1(symbols _ _ _ I _ _ (member b)));unfold word64;lia. Qed.
Theorem checked (root:cpu) bias e op : placement e -> loaded root bias e ->
 contract root (writable e) (CallLayout.stack_area e) (CallLayout.base bias+site op) (CallLayout.base bias+(site op+5))
   (8+depth op) (code op) (call bias op).
Proof.
 intros P I;unfold call.
 eapply (invoke _ _ _ _ _ _ (disp op) _ _ 0xadd).
 - exact (stack_available e P).
 - destruct op;cbn [depth];lia.
 - exact (proj2(symbols _ _ _ I _ _ builder_in)).
 - exact (proj2(symbols _ _ _ I _ _ decoder_in)).
 - destruct op;cbn [site];lia.
 - apply sites.
 - lia.
 - vm_compute;reflexivity.
 - replace (CallLayout.base bias+(site op+5)+disp op) with (bias+DecoderBytes.address+target op) by
    (unfold CallLayout.base,disp;ring).
   apply (fits root bias e I DecoderKernel.Carry);change (0<=target op<2984);destruct op;cbn [target];lia.
 - destruct(proj1(symbols _ _ _ I _ _ builder_in)) as [L H].
   change (Z.of_nat(length CallLayout.text)) with 2280 in H.
   change (0<=bias+CallLayout.origin) in L;change (bias+CallLayout.origin+2280<=2^64) in H.
   unfold CallLayout.base,word64;destruct op;cbn [site];lia.
 - replace (CallLayout.base bias+(site op+5)+disp op) with (bias+DecoderBytes.address+target op) by
    (unfold CallLayout.base,disp;ring).
   destruct op;[exact (NativeProduct.check_product bias root (writable e) (stack_area e)
       (stack_available _ P) (placed _ _ _ I) (fits _ _ _ I))|..];
    exact (NativeProduct.calc bias root (writable e) (stack_area e) (placed _ _ _ I) DecoderKernel.Carry).
Qed.

Lemma preserves_words bias op : ProcedureWords.words(call bias op).
Proof.
 apply ProcedureWords.call;destruct op;unfold body,NativeProduct.product,NativeProduct.columns,NativeProduct.native;
 repeat first [apply ProcedureWords.sequence|apply ProcedureWords.call|apply ProcedureWords.block].
Qed.
