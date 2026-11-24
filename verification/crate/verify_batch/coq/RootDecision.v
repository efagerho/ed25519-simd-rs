From Coq Require Import ZArith Bool Lia Ring.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Curve25519 Require Import Field Radix51.
From Curve25519.group Require Import PrimeField Affine Decompression RootCriterion.
From Ed25519Simd.Decode Require Import Limbs.
From Ed25519Simd.Decode Require Decode Kernels.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchDecode KeySquare NativeScale.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderFinish DecoderPower PowerInputs PowerWrites RootTest RootAccept PairedSetup SetupTail.
Local Open Scope Z_scope.

Definition decodable e j:=exists x,on_curve x (residue (original_encoding false e j mod 2^255)).
Lemma uv_field y : residue (PowerInputs.uv y)=(numerator(residue y)*denominator(residue y))%fp.
Proof. unfold PowerInputs.uv,denominator,numerator;repeat first [rewrite residue_mul|rewrite residue_sub];reflexivity. Qed.
Lemma test_field y :
 let v:=PowerInputs.uv y in let t:=v^Decompression.exponent in
 residue (t*t*v)=test_value (numerator(residue y)) (denominator(residue y))
   (Decompression.power (numerator(residue y)*denominator(residue y))%fp Decompression.exponent).
Proof.
 cbv zeta;rewrite !residue_mul,Decode.pow_value by (vm_compute;discriminate || reflexivity);
 rewrite uv_field;unfold test_value;ring.
Qed.

Theorem bits pol bias e r : RootTest.post pol bias e r -> forall j,(j<8)%nat ->
 RootAccept.bits false e (machine(RootTest.at_test r)) j=true <-> decodable e j.
Proof.
 intros Out j J;set (q:=vectors(machine(RootTest.at_test r)) j).
 set (t:=PowerWrites.before_power(RootTest.power r));set (s:=SetupTail.after_square(PowerInputs.half t false)).
 set (h:=vectors(machine s) j);set (u:=row (machine(RootTest.at_test r)) (point e false) j).
 set (y:=original_encoding false e j mod 2^255);set (fy:=residue y).
 pose proof(RootTest.root_test _ _ _ _ Out j J) as [Bq [Low Q]];fold y q in Bq,Low,Q.
 pose proof(RootTest.setup_fields_live _ _ _ _ Out false) as F.
 assert (U:forall i,(i<5)%nat -> u i=u_digits h i) by (intros i I;exact (proj1(F j i J I))).
 destruct(RootTest.power_result _ _ _ _ Out) as [D _].
 destruct D as [Both _];destruct Both as [[KeySq _] _];change (KeySquare.squared false pol bias e s) in KeySq;destruct KeySq as [_ [_ [_ [_ Square]]]].
 destruct(Square j J) as [Bound [YY Pos]];fold y h in Bound,YY,Pos.
 assert (H:bounded h) by (intros i I;specialize(Bound i I);change (0<=h i<=radix+2^16) in Bound;lia).
 assert (B:bounded q) by (intros i I;specialize(Bq i I);lia).
 assert (P:1<pack q).
 { unfold pack,limbs;pose proof(B 1%nat ltac:(lia));pose proof(B 2%nat ltac:(lia));pose proof(B 3%nat ltac:(lia));pose proof(B 4%nat ltac:(lia));
   unfold Radix51.radix in *;lia. }
 assert (Qfield:Decode.value q=test_value (numerator fy) (denominator fy)
     (Decompression.power (numerator fy*denominator fy)%fp Decompression.exponent)).
 { apply Decode.congruent_value in Q;unfold Decode.value,pack;rewrite Q;apply test_field. }
 assert (Ufield:Decode.value (u_digits h)=numerator fy).
 { destruct(scaled_values h) as [Rep _].
   assert (Ueq:represents (pack(u_digits h)) (121666*(y*y-1))) by
     (eapply ctrans;[exact Rep|apply ctimes;[apply crefl|apply cminus;[exact YY|apply crefl]]]).
   apply Decode.congruent_value in Ueq;unfold Decode.value;rewrite Ueq;unfold fy,numerator;rewrite !residue_mul,residue_sub,residue_mul;reflexivity. }
 assert (Test:forall d,-1<=d<=1 -> (high_test q d=true <-> Decode.value q=residue d)).
 { intros d Delta;rewrite high_test_correct by assumption;apply Decode.congruent_value. }
 assert (Zero:high_test u 0=true <-> numerator fy=0%fp).
 { replace (high_test u 0) with (high_test (u_digits h) 0) by (unfold high_test;rewrite !U by lia;reflexivity).
   rewrite u_test_correct by assumption;rewrite Decode.congruent_value;rewrite <-Ufield;reflexivity. }
 assert (Plus:high_test q 1=true <-> Decode.value q=1%fp) by (apply Test;lia).
 assert (Minus:high_test q (-1)=true <-> Decode.value q=(0-1)%fp) by (apply Test;lia).
 change ((high_test q 1 || high_test u 0 || high_test q (-1))%bool=true <-> exists x,on_curve x fy).
 rewrite !orb_true_iff,Plus,Minus,Zero,Qfield;rewrite <-root_criterion;tauto.
Qed.
