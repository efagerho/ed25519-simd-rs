From Coq Require Import ZArith Lia List.
From Coqprime.elliptic Require GZnZ.
From Machine Require Import memory.ByteMemory execution.LinkedCalls execution.MaskTrace.
From ProofArithmetic Require Import Radix.
From Curve25519 Require Import Field Scalar Edwards Radix51.
From Curve25519.group Require Import PrimeField Affine Representation Decompression SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.PostHash Require Export Lanes.
From Ed25519Simd.Dalek Require Import Encoding.
From Ed25519Simd.Decode Require Import Decode Chunks.
From Ed25519Simd.Scalar Require Import ScalarSpec.
From Ed25519Simd.FullLadder Require Import Operands.
From Ed25519Simd.FullLadder Require Audit Object LinkedBytes.
From Ed25519Simd.Radix16 Require Audit Object LinkedBytes.
From Ed25519Simd.Torsion Require Audit Object ObjectBytes.
Local Open Scope Z_scope.

Definition encoded_point w R :=
 y R = residue (w mod 2^255) /\ has_sign (Z.testbit w 255) (x R).
Definition accepts w Q := exists R, encoded_point w R /\
 multiple 8 (plus Q (negative R)) = identity.

Lemma exact_accepts flat ptr j Q : byte_memory flat ->
 Unpack.encoded flat ptr j = compress Q -> accepts (Unpack.encoded flat ptr j) Q.
Proof.
 intros B E. apply (encoding_equal flat ptr j Q B) in E as [Y X].
 exists Q. split.
 - split;[rewrite Y; destruct (y Q) as [v E]; unfold residue; apply GZnZ.zirr; cbn; exact E|right;auto].
 - rewrite plus_negative. cbn [multiple]; now rewrite !plus_identity.
Qed.

Definition cofactor Q R := multiple 8 (plus Q (negative R))=identity.
(* Interface for the point written by the decoder. All four coordinates have
   their specified field values even if the decode-valid bit is clear. *)
Lemma decoded_accepts k flat ptr pair j w Q q mask lane :
 Chunks.lane_claim k flat ptr pair j ->
 w=read_le 32 flat (ptr+32*Z.of_nat j) ->
 represents_point true q Q ->
 Ed25519Simd.Torsion.Audit.lane_result mask lane q
    (coordinates_of (Chunks.lane_output k flat ptr pair j)) ->
 ((Z.testbit (Chunks.returned k flat ptr pair) (Z.of_nat j) &&
   Z.testbit mask (Z.of_nat lane))%bool=true <-> accepts w Q).
Proof.
 intros H -> CQ [_ T]. unfold lane_claim in H.
 set (o:=Chunks.lane_output k flat ptr pair j) in *.
 set (w:=read_le 32 flat (ptr+32*Z.of_nat j)) in *.
 destruct H as [_ [_ [_ [_ [_ [Y [Zr [TT Meaning]]]]]]]].
 destruct (Z.testbit (Chunks.returned k flat ptr pair) (Z.of_nat j)).
 - destruct Meaning as [C [S U]]. set (R:=Point _ _ C).
   assert (Rep:represents_point true (coordinates_of o) R).
   { unfold represents_point,represents_xyz,coordinates_of; cbn [cx cy cz ct x y].
     fold (value (ox o)) (value (oy o)) (value (oz o)) (value (ot o)).
     subst R; cbn [x y]. rewrite Zr,Y,TT. split;[split;[discriminate|split;ring]|intros;ring]. }
   specialize(T Q R CQ Rep Zr). cbn [andb]. rewrite T.
   split;[intro E;exists R;split;[split;[reflexivity|exact S]|exact E]|].
   intros [P [[YP SP] E]]. assert (P=R).
   { apply point_ext. split;[apply U;[rewrite <-YP;apply on_edwards|exact SP]|exact YP]. }
   now subst P.
 - cbn [andb]. split;[discriminate|]. intros [P [[YP _] _]]. exfalso.
   apply (Meaning (x P));rewrite <- YP;apply on_edwards.
Qed.
