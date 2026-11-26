From Ed25519Simd.Decode Require NativeProduct.
From Curve25519.group Require Import PointDecoding.
From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.FlatMemory memory.ByteMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Return BatchDecode KeySquare NativeScale RootValue DecodedRows.
From Ed25519Simd.VerifyBatch Require RootOperands SignatureDecision PairReturn.
Local Open Scope Z_scope.
Local Opaque NativeProduct.kernel Power.apply_kernel.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem checked pol bias e t : placement e -> PairReturn.post pol bias e t ->
 geometry true e (buffer true e (machine(PairReturn.returned t))).
Proof.
 intros P Pair;set (f:=PairReturn.signature t);set (s:=PairReturn.sig_entry t).
 pose proof(PairReturn.signature_entry _ _ _ _ Pair) as Entry;fold s in Entry.
 pose proof(PairReturn.signature_result _ _ _ _ Pair) as Done;fold s f in Done.
 destruct(SignatureDecision.inputs _ _ _ _ P Pair) as [sq [Square [Operands Fields]]];fold f s in Operands,Fields.
 pose proof(FinishTrace.test_result _ _ _ _ _ _ Done) as Product.
 pose proof(RootTest.at_comparison _ _ _ _ _ _ Operands Product) as Test.
 apply (DecodedRows.returned true pol bias e (FinishTrace.signed f) _ (FinishTrace.coordinates _ _ _ _ _ _ Done)).
 intros j J;set (w:=original_encoding true e j);set (cmp:=FinishTrace.test f).
 destruct(RootOperands.factor true pol bias e s cmp (FinishTrace.validity f) j Entry Operands Product
    (FinishTrace.factor_pointer _ _ _ _ _ _ Done) (FinishTrace.validity_memory _ _ _ _ _ _ Done) J) as [T TV].
 destruct(RootOperands.numerator true pol bias e sq cmp (FinishTrace.validity f) j Square Test
    (fun k i K I=>proj1(Fields k i K I)) (fun i I=>FinishTrace.numerator _ _ _ _ _ _ Done j i I) J) as [U [UV Bit]].
 destruct(FinishTrace.choice _ _ _ _ _ _ Done) as [ks Chosen].
 destruct(RootValue.registers true pol bias e (FinishTrace.validity f) (FinishTrace.raw f) (FinishTrace.chosen f)
    (FinishTrace.test_masks f) ks j w (FinishTrace.raw_result _ _ _ _ _ _ Done) Chosen J U UV T TV) as [B V].
 destruct Entry as [_ [_ [_ [_ [_ [_ [_ [_ [Tag _]]]]]]]]].
 assert (Sign:Z.testbit (regs(machine(FinishTrace.chosen f)) 9%nat) (Z.of_nat j)=encoded_sign w)
    by (rewrite (FinishTrace.sign_register _ _ _ _ _ _ Done);apply Tag,J).
 destruct(RootValue.signed (machine(FinishTrace.chosen f)) j w (vectors(machine(FinishTrace.signed f)) j) B Sign
    (fun i I=>FinishTrace.sign _ _ _ _ _ _ Done j i J I)) as [X Value].
 assert (Y:same (row (machine(FinishTrace.signed f)) (BatchDecode.point e true+320) j)
                (row (machine cmp) (BatchDecode.point e true+320) j)).
 { intros i I;eapply SetupValues.keep_row;[exact (FinishTrace.y_memory _ _ _ _ _ _ Done)|unfold span;lia|exact J|exact I]. }
 destruct(RootOperands.y_at_test _ _ _ _ _ _ Square Fields j J) as [BY YV].
 split;[exact X|split;[intros i I;rewrite Y by exact I;apply BY,I|split;[etransitivity;[apply Radix51.limbs_ext,Y|exact YV]|]]].
 intros G Dec;rewrite Value,V;apply decoded_x;[rewrite (proj2(FinishTrace.mask_bit _ _ _ _ _ _ Done j J));exact Bit|exact Dec].
Qed.
End Iteration.
