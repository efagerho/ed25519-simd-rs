From Coq Require Import ZArith Lia List.
From Curve25519 Require Import Torsion group.Cofactor.
From Machine Require Import execution.MaskTrace execution.CircuitFacts.
From Ed25519Simd.field51 Require Import RootMasks.
From Ed25519Simd.Torsion Require Import Program Schedule Audit Lane ObjectBytes.
Local Open Scope Z_scope.

(* A successful all-lanes comparison returns the comparison mask itself.
   Every other mask selects the complete per-lane test. *)
Local Lemma select_mask (quick full:nat->Z) (P:nat->Prop) :
 (forall j,(j<8)%nat -> (quick j=0 \/ quick j=1) /\ (quick j=1 -> P j)) ->
 (forall j,(j<8)%nat -> bit_spec (full j) (P j)) ->
 let mask:=if mask_word 8 quick =? 255 then mask_word 8 quick else mask_word 8 full in
 0<=mask<256 /\ forall j,(j<8)%nat -> (Z.testbit mask (Z.of_nat j)=true <-> P j).
Proof.
 intros Q F. destruct (Z.eqb_spec (mask_word 8 quick) 255) as [All|Miss].
 - rewrite All. split; [lia|]. intros j J.
   destruct (mask_word_bits 8 quick (fun j H=>proj1(Q j H))) as [_ Bits].
   rewrite All in Bits. split;[intro B;exact(proj2(Q j J)(proj1(Bits j J) B))|].
   intros _. change 255 with (Z.ones 8). apply Z.ones_spec_low;lia.
 - destruct (mask_word_bits 8 full (fun j H=>proj1(F j H))) as [Range Bits].
   split;[exact Range|]. intros j J;rewrite Bits by assumption;exact(proj2(F j J)).
Qed.

Local Lemma branch_result t a x b y inputs ini :
 t = Branch a x 255 (Exit a x) (Exit b y) ->
 result t inputs ini = Some (if mask_value a x inputs ini =? 255 then
     mask_value a x inputs ini else mask_value b y inputs ini).
Proof. intros ->;cbn [result];destruct (mask_value a x inputs ini =? 255);reflexivity. Qed.

Local Lemma full_meaning mask q r :
 (0 <= mask < 256 /\ forall j, (j < 8)%nat ->
   (Z.testbit mask (Z.of_nat j) = true <-> torsion_check (q j) (r j))) ->
 0 <= mask < 256 /\ forall j, (j < 8)%nat -> lane_result mask j (q j) (r j).
Proof.
 intros [Range Bits]. split; [exact Range|]. intros j J. specialize (Bits j J).
 split; [exact Bits|]. intros P R Q A AffineR.
 rewrite Bits. exact (torsion_check_correct _ _ P R Q A AffineR).
Qed.

Local Opaque result short long.
Theorem assembled_torsion_correct : torsion_contract symbol_bytes.
Proof.
 constructor; [vm_compute;reflexivity | vm_compute;reflexivity |].
 intros pad p r ini Pad Bounds. rewrite (branch_result _ _ _ _ _ _ _ (paths_checked pad Pad)).
 eexists;split;[reflexivity|].
 apply full_meaning, select_mask.
 - intros j J. destruct (early_lane p r ini j J Bounds) as [Bit Det].
   split;[exact Bit|]. intro B. apply determinant_zero_accepts, Det, B.
 - intros j J;apply full_lane;assumption.
Qed.
