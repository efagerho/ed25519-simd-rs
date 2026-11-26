From Curve25519.group Require Import DecompressionDigits.
From Curve25519.group Require Import PointDecoding.
From Coq Require Import ZArith Bool Lia Ring.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Curve25519 Require Import Field Radix51.
From Curve25519.group Require Import PrimeField Affine Decompression RootCriterion.
From Curve25519 Require Import Radix51Digits DecompressionRadix51.
From Ed25519Simd.Decode Require Decode Kernels.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchDecode KeySquare NativeScale.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderFinish DecoderPower PowerInputs PowerWrites RootTest RootAccept PairedSetup SetupTail.
Local Open Scope Z_scope.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition decodes sig e j:=exists x,on_curve x (residue (original_encoding sig e j mod 2^255)).
Definition decodable:=decodes false.
Lemma comparison_values sig pol bias e sq cmp :
 KeySquare.squared sig pol bias e sq -> RootTest.math sig e cmp ->
 (forall j i,(j<8)%nat -> (i<5)%nat ->
  row (machine cmp) (point e sig) j i=u_digits (vectors(machine sq) j) i) ->
 forall j,(j<8)%nat -> let fy:=residue (original_encoding sig e j mod 2^255) in
 let u:=row (machine cmp) (point e sig) j in let q:=vectors(machine cmp) j in
 split_field u /\ Decode.value u=numerator fy /\
 (high_test q (-1)=true <-> root_test fy=(0-1)%fp) /\
 (RootAccept.bits sig e (machine cmp) j=true <-> decodes sig e j).
Proof.
 intros [_ [_ [_ [_ Square]]]] Math Numerator j J.
 set (q:=vectors(machine cmp) j);set (h:=vectors(machine sq) j);set (u:=row (machine cmp) (point e sig) j).
 set (y:=original_encoding sig e j mod 2^255);set (fy:=residue y).
 destruct(Math j J) as [Bq [Low Q]];fold y q in Bq,Low,Q.
 assert (U:forall i,(i<5)%nat -> u i=u_digits h i) by (intros i I;apply Numerator;assumption).
 destruct(Square j J) as [Bound [YY Pos]];fold y h in Bound,YY,Pos.
 assert (H:bounded h) by (intros i I;specialize(Bound i I);change (0<=h i<=radix+2^16) in Bound;lia).
 assert (B:bounded q) by (intros i I;specialize(Bq i I);lia).
 assert (P:1<pack q) by (apply positive_from_low; assumption).
 assert (Qfield:Decode.value q=test_value (numerator fy) (denominator fy)
     (Decompression.power (numerator fy*denominator fy)%fp Decompression.exponent)).
 { apply PrimeField.congruent_value in Q;unfold Decode.value,pack;rewrite Q;apply test_field. }
 assert (Ufield:Decode.value (u_digits h)=numerator fy).
 { exact (proj1 (setup_field _ _ YY)). }
 assert (Test:forall d,-1<=d<=1 -> (high_test q d=true <-> Decode.value q=residue d)).
 { intros d Delta;rewrite high_test_correct by assumption;apply PrimeField.congruent_value. }
 assert (Zero:high_test u 0=true <-> numerator fy=0%fp).
 { replace (high_test u 0) with (high_test (u_digits h) 0) by (unfold high_test;rewrite !U by lia;reflexivity).
   rewrite u_test_correct by assumption;rewrite PrimeField.congruent_value;rewrite <-Ufield;reflexivity. }
 assert (Plus:high_test q 1=true <-> Decode.value q=1%fp) by (apply Test;lia).
 assert (Minus:high_test q (-1)=true <-> Decode.value q=(0-1)%fp) by (apply Test;lia).
 split.
 { intros i I;rewrite U by exact I;exact (bounded_split _ (proj1(scaled_bounds h H Pos)) i I). }
 split;[unfold Decode.value,pack;erewrite limbs_ext by exact U;exact Ufield|].
 split;[rewrite Minus,Qfield;reflexivity|].
 change ((high_test q 1 || high_test u 0 || high_test q (-1))%bool=true <-> exists x,on_curve x fy).
 rewrite !orb_true_iff,Plus,Minus,Zero,Qfield;rewrite <-root_criterion;tauto.
Qed.

Lemma from_comparison sig pol bias e sq cmp :
 KeySquare.squared sig pol bias e sq -> RootTest.math sig e cmp ->
 (forall j i,(j<8)%nat -> (i<5)%nat -> row (machine cmp) (point e sig) j i=u_digits (vectors(machine sq) j) i) ->
 forall j,(j<8)%nat -> RootAccept.bits sig e (machine cmp) j=true <-> decodes sig e j.
Proof. intros S M U j J;exact (proj2(proj2(proj2(comparison_values _ _ _ _ _ _ S M U j J)))). Qed.

Theorem bits pol bias e r : RootTest.post pol bias e r -> forall j,(j<8)%nat ->
 RootAccept.bits false e (machine(RootTest.at_test r)) j=true <-> decodable e j.
Proof.
 intro R;set (t:=PowerWrites.before_power(RootTest.power r)).
 apply (from_comparison false pol bias e (SetupTail.after_square(PowerInputs.half t false))).
 - exact (proj1(proj1(proj1(proj1(RootTest.power_result _ _ _ _ R))))).
 - exact (RootTest.root_test _ _ _ _ R).
 - intros j i J I;exact (proj1(RootTest.setup_fields_live _ _ _ _ R false j i J I)).
Qed.

Lemma signed_encoding sig e j : decodes sig e j <->
 exists a,PointEncoding.decodes (BatchDecode.original_encoding sig e j) a.
Proof. apply PointEncoding.signed_encoding. Qed.
End Iteration.
