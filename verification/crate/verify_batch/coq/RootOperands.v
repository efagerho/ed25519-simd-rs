From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory.
From Curve25519 Require Import Field Radix51.
From Curve25519.group Require Import PrimeField Affine Decompression.
From Ed25519Simd.Decode Require Import Limbs Decode.
From Ed25519Simd.VerifyBatch Require Import Policy BatchDecode KeySquare NativeScale RootDecision RootValue.
From Ed25519Simd.VerifyBatch Require RootTest FinishProduct Selection.
Local Open Scope Z_scope.

(* The first multiply of the finish helper uses the live numerator in ZMM
   registers and the paired power result at the address in RSI. *)
Lemma factor sig pol bias e start cmp valid j :
 DecoderFinish.entry sig pol bias e start -> RootTest.operands sig pol e start -> FinishProduct.post sig pol bias e start cmp ->
 regs(machine valid) 6%nat=regs(machine cmp) 6%nat -> mem(machine valid)=mem(machine cmp) -> (j<8)%nat ->
 let t:=row (machine valid) (regs(machine valid) 6%nat) j in
 split_field t /\ value t=power_value (fy(original_encoding sig e j)).
Proof.
 intros [_ [_ [_ [_ [_ [SI _]]]]]] Input [_ [_ [_ [G [Keep _]]]]] Reg Mem J t.
 set (src:=FinishSquare.operand sig pol e (machine start) j);destruct(Input j J) as [Squared [_ [Power _]]];fold src in Squared,Power.
 assert (Same:same t src).
 { intros i N;unfold t,src,FinishSquare.operand;rewrite Reg,G,SI by discriminate.
   unfold row at 1;rewrite Mem;apply (SetupValues.keep_row _ _ _ _ Keep);[|exact J|exact N].
   unfold DecoderFinish.power_offset;destruct sig;lia. }
 split;[apply (same_split _ _ Same),squared_split,Squared|rewrite (same_value _ _ Same)].
 apply congruent_value in Power;unfold value,pack;rewrite Power,Decode.pow_value by (vm_compute;discriminate || reflexivity).
 rewrite RootDecision.uv_field;reflexivity.
Qed.

Lemma y_at_test sig pol bias e sq cmp :
 KeySquare.squared sig pol bias e sq -> SetupValues.fields sig e sq cmp ->
 forall j,(j<8)%nat -> let y0:=row (machine cmp) (BatchDecode.point e sig+320) j in
 radix_digits y0 /\ limbs y0=original_encoding sig e j mod 2^255.
Proof.
 intros [_ [_ [_ [In _]]]] Fields j J y0;destruct(In j J) as [B [Y _]].
 assert (E:same y0 (DecoderSave.digits sig e (machine sq) j)) by
   (intros i I;exact (proj2(proj2(proj2(Fields j i J I))))).
 split;[intros i I;rewrite E by exact I;apply B,I|rewrite <-Y;apply limbs_ext,E].
Qed.

Lemma numerator sig pol bias e sq cmp valid j :
 KeySquare.squared sig pol bias e sq -> RootTest.math sig e cmp ->
 (forall lane i,(lane<8)%nat -> (i<5)%nat -> row (machine cmp) (BatchDecode.point e sig) lane i=u_digits (vectors(machine sq) lane) i) ->
 same (vectors(machine valid) j) (row (machine cmp) (BatchDecode.point e sig) j) -> (j<8)%nat ->
 split_field(vectors(machine valid) j) /\ value(vectors(machine valid) j)=Decompression.numerator (fy(original_encoding sig e j)) /\
 (high_test (vectors(machine cmp) j) (-1)=true <-> test(fy(original_encoding sig e j))=(0-1)%fp).
Proof.
 intros S T U E J;destruct(comparison_values _ _ _ _ _ _ S T U j J) as [Bound [V [M _]]];
 split;[exact (same_split _ _ E Bound)|rewrite (same_value _ _ E);auto].
Qed.
