From Coq Require Import ZArith Lia List.
From Coqprime.elliptic Require GZnZ.
From Machine Require Import memory.ByteMemory execution.LinkedCalls execution.MaskTrace.
From ProofArithmetic Require Import Radix.
From Curve25519 Require Import Field Scalar Edwards Radix51.
From Curve25519.group Require Import PrimeField Affine Representation Decompression SignedMultiple.
From Ed25519Simd Require Import Wide51.
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

(* Combine the reducer's actual return memory and the full ladder execution.
   The call boundary passes the same 512 digit bytes to R8. *)
Module D := Ed25519Simd.Radix16.Audit.
Module F := Ed25519Simd.FullLadder.Audit.
Definition challenge s j := lane_input (buffer_words (LinkedCalls.mem s) (LinkedCalls.regs s 6%nat)) j mod L.
Definition candidate s l B A j :=
 plus (scale (number 16 (digit_list l 1 j)) B) (scale (-challenge s j) (A j)).

Definition product_correct :=
 forall slide s l mid out B A ip,
 let target := Ed25519Simd.Radix16.LinkedBytes.reducer_pc in
 let pc := Ed25519Simd.Radix16.LinkedBytes.wrapper_pc in
 let bytes := Ed25519Simd.Radix16.LinkedBytes.symbol_bytes in
 let n := D.size bytes in let dst := LinkedCalls.regs s 7%nat in
 D.placement (LinkedCalls.regs s 4%nat) dst (LinkedCalls.regs s 6%nat) (slide+pc) n (slide+target)
    (D.size Ed25519Simd.Scalar.ObjectBytes.symbol_bytes) -> LinkedCalls.well_formed s ->
 D.run slide pc target n s ip mid ->
 (forall j, (j<8)%nat -> digit_list l 8 j = D.signed_digits (LinkedCalls.mem mid) dst j) ->
 F.placement slide l -> LinkedCalls.regs l 9%nat=1 ->
 valid_inputs (slide+Ed25519Simd.FullLadder.LinkedBytes.stage_pc) (F.pad_of l) l ->
 valid_tables l B A -> F.execution slide l true out ->
 strict out /\ forall j,(j<8)%nat -> represents_point true (point_values out j) (candidate s l B A j).
Lemma product_ok : product_correct.
Proof.
 intros slide s l mid out B A ip target pc bytes n dst P W Run Dig PL T I V LRun.
 destruct (D.run_correct _ _ _ _ Ed25519Simd.Radix16.Object.assembled_digest_to_radix16_correct
    slide s P W) as [v [_ [Unique [_ [_ [_ [_ Digits]]]]]]].
 destruct (Unique _ _ Run) as [_ ->].
 destruct (F.full_product Ed25519Simd.FullLadder.Object.assembled_full_ladder_correct
  slide l true B A PL T I V) as [_ Result].
 destruct (Result out LRun) as [Bound [Reps _]]. split;[exact Bound|].
 intros j J. specialize (Reps j J). rewrite Dig in Reps by exact J.
 unfold dst in Reps; rewrite (proj2 (Digits j J)) in Reps. exact Reps.
Qed.

Definition cofactor Q R := multiple 8 (plus Q (negative R))=identity.
(* Interface for the point written by the decoder. All four coordinates have
   their specified field values even if the decode-valid bit is clear. *)
Definition coordinates_of (o:output) := Coordinates (Limbs.pack (ox o)) (Limbs.pack (oy o))
  (Limbs.pack (oz o)) (Limbs.pack (ot o)).
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
