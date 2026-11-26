From Ed25519Simd.Decode Require NativeProduct.
From Curve25519.group Require Import PointDecoding.
From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.FlatMemory memory.ByteMemory.
From Curve25519 Require Import Radix51.
From Ed25519Simd.Decode Require Import Decode.
From Ed25519Simd.VerifyBatch Require Import Policy Return BatchDecode KeySquare NativeScale RootValue DecodedRows.
From Ed25519Simd.VerifyBatch Require RootOperands KeyReturn.
Local Open Scope Z_scope.
Local Opaque NativeProduct.kernel Power.apply_kernel.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem checked pol bias e t : placement e -> KeyReturn.post pol bias e t ->
 geometry false e (buffer false e (machine(KeyReturn.returned t))).
Proof.
 intros P K;set (sr:=KeyReturn.signed t) in *;pose proof(KeyReturn.signed_result _ _ _ _ K) as S;fold sr in S.
 pose proof(SignedRoot.raw _ _ _ _ S) as R;pose proof(RootCandidate.native _ _ _ _ R) as Raw;pose proof(RootCandidate.selection _ _ _ _ R) as Pick.
 pose proof(Selection.test_result _ _ _ _ Pick) as Test;destruct(SignedRoot.selection _ _ _ _ S) as [ks Chosen].
 set (r:=Selection.test(RootCandidate.decision(SignedRoot.candidate sr))) in *.
 set (cmp:=RootTest.at_test r) in *;set (start:=RootTest.finish_entry r) in *.
 set (valid:=Selection.selection(RootCandidate.decision(SignedRoot.candidate sr))) in *.
 set (sq:=SetupTail.after_square(PowerInputs.half (PowerWrites.before_power(RootTest.power r)) false)).
 assert (Square:KeySquare.squared false pol bias e sq) by exact (proj1(proj1(proj1(proj1(RootTest.power_result _ _ _ _ Test))))).
 pose proof(RootTest.setup_fields_live _ _ _ _ Test false) as Fields;fold cmp sq in Fields.
 pose proof(RootTest.root_product _ _ _ _ Test) as Product;fold start cmp in Product.
 pose proof(RootTest.finish_arguments _ _ _ _ Test) as Args;fold start in Args.
 apply (DecodedRows.returned false pol bias e (SignedRoot.at_store sr) _ (KeyReturn.native_return _ _ _ _ K)).
 intros j J;set (w:=original_encoding false e j).
 destruct(RootOperands.factor false pol bias e start cmp valid j Args (RootTest.initial_operands _ _ _ _ Test false) Product
    (Selection.scalar_registers _ _ _ _ Pick 6%nat ltac:(discriminate)) (Selection.test_memory _ _ _ _ Pick) J) as [T TV].
 destruct(RootOperands.numerator false pol bias e sq cmp valid j Square (RootTest.root_test _ _ _ _ Test)
   (fun lane i L I=>proj1(Fields lane i L I)) (fun i I=>Selection.numerator _ _ _ _ Pick j i I) J) as [U [UV TestBit]].
 set (m:=Selection.masks(RootCandidate.decision(SignedRoot.candidate sr))) in *.
 destruct(RootValue.registers false pol bias e valid (RootCandidate.saved_x(SignedRoot.candidate sr)) (SignedRoot.selected sr) m ks j w
    Raw Chosen J U UV T TV) as [BX VX].
 destruct Args as [_ [_ [_ [_ [_ [_ [_ [_ [Tag _]]]]]]]]].
 assert (Sign:Z.testbit (regs(machine(SignedRoot.selected sr)) 9%nat) (Z.of_nat j)=encoded_sign w).
 { rewrite (RootAdjusted.gprs _ _ _ _ _ _ _ Chosen),(RootCandidate.saved_register _ _ _ _ R) by discriminate;exact (Tag j J). }
 destruct(RootValue.signed (machine(SignedRoot.selected sr)) j w (vectors(machine(SignedRoot.at_store sr)) j) BX Sign
  (fun i I=>SignedRoot.sign _ _ _ _ S j i J I)) as [X Value].
 assert (Y:same (row (machine(SignedRoot.at_store sr)) (BatchDecode.point e false+320) j)
       (row (machine cmp) (BatchDecode.point e false+320) j)).
 { intros i I;destruct Product as [_ [_ [_ [_ [Keep _]]]]];pose proof(depth pol e);destruct(scratch_stack _ P);
   apply (SetupValues.keep_row _ _ _ (fun x=>BatchDecode.point e false+320<=x<BatchDecode.point e false+640));
   try lia;try exact J;try exact I;intros x Hit;rewrite Keep,(SignedRoot.before_x _ _ _ _ S).
   all: try reflexivity;unfold SignedRoot.protected,BatchDecode.point,BatchDecode.point_offset,disjoint in *;lia. }
 destruct(RootOperands.y_at_test _ _ _ _ _ _ Square Fields j J) as [BY YV].
 split;[exact X|split;[intros i I;rewrite Y by exact I;apply BY,I|split;[etransitivity;[apply Radix51.limbs_ext,Y|exact YV]|]]].
 intros G Dec;rewrite Value,VX;apply decoded_x;[unfold m;rewrite (proj2(Selection.accepts_key _ _ _ _ Pick j J));exact TestBit|exact Dec].
Qed.
End Iteration.
