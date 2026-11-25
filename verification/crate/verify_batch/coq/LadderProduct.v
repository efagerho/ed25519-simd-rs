From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Curve25519.group Require Import Affine Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.FullLadder Require Object.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require LadderLayout.
Local Open Scope Z_scope.

(* Apply the linked full-product theorem to the CPU actually invoked by the
   candidate. This component exposes the returned point as a word buffer. *)
Definition meaning pol bias e t:Prop:= let run:=FullLadder.Audit.execution bias (machine t) (LadderEntry.full pol) in
 (exists out,run out) /\ forall out,run out -> strict out /\
 forall j A,(j<8)%nat -> HashLayout.eligible pol e j ->
 Policy.decodes (little_endian(key_bytes(HashLayout.row e j))) A ->
 represents_point (LadderEntry.full pol) (point_values out j)
   (plus (scale (little_endian(s_bytes(HashLayout.row e j))) generator)
         (scale (-Policy.challenge(HashLayout.row e j)) A)).

Theorem checked pol bias e p t : loaded pol bias (mem e) (writable e) -> Tables.mapped e bias -> Candidate.constants e ->
 ProductRun.geometry (HashLayout.chunk pol e bias) -> LadderEntry.entry pol bias e p t ->
 meaning pol bias e t.
Proof.
 intros I Map Const G E;unfold meaning;cbv zeta;destruct(LadderLayout.checked _ _ _ _ _ G E) as [P V].
 destruct(LadderEntry.arguments _ _ _ _ _ E) as [_ [_ [_ [_ [_ [_ Mode]]]]]].
 destruct(FullLadder.Audit.full_product FullLadder.Object.assembled_full_ladder_correct bias (machine t)
   (LadderEntry.full pol) generator (LadderTables.key e) P Mode V (LadderTables.supplied _ _ _ _ _ I Map Const E))
   as [Live Result];split;[exact Live|].
 intros out R;destruct(Result out R) as [Bounds [Points _]];split;[exact Bounds|].
 intros j A J On Key;specialize(Points j J).
 destruct(LadderLayout.signature_digits _ _ _ _ _ _ E J) as [_ S].
 rewrite (S (proj1 On)),(proj2(LadderEntry.challenge _ _ _ _ _ E j J) On) in Points.
 assert (K:LadderTables.key e j=A).
 { unfold LadderTables.key;destruct(LadderTables.choice (BatchDecode.original_encoding false e j)) as [D|[Bad _]].
   - exact (Lane.unique_key _ _ _ D Key).
   - exfalso;exact (Bad A Key). }
 now rewrite K in Points.
Qed.
