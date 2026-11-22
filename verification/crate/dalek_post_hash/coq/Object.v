From Coq Require Import List ZArith Bool Lia.
From Curve25519 Require Import Radix51.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.FullLadder Require Import Operands.
From Ed25519Simd.Decode Require Import Program Unpack.
From Ed25519Simd.Dalek Require Import Batch.
From Ed25519Simd.PostHash Require Import Product Staging.
From Ed25519Simd.Zip215 Require Import Schedule.
From Ed25519Simd.DalekPostHash Require Import Caller Binding Screen Keys Decoded Queue Audit.
Import ListNotations. Local Open Scope Z_scope.

Lemma observed b q : candidate_returns b q ->
 valid_chunk q (product b) /\ valid_tables(ladder_entry b)(base b)(key b).
Proof.
 intros [slide [mid [ip Calls]]]. destruct(product_ok false _ _ _ _ _ _ _ _ Calls) as [Strict Reps].
 split;[split|exact (ladder_tables _ _ _ _ _ _ (entry_inputs _ _ _ _ _ _ _ _ _ Calls))].
 - intros row j R J;apply (strict_split _ Strict);cbn;lia.
 - intros;apply Reps;assumption.
Qed.
Lemma filtered_ok b j : valid_tables(ladder_entry b)(base b)(key b) -> (j<8)%nat ->
 (eligible(filtered b) j=true <-> eligible(metadata b) j=true /\ Affine.multiple 8(key b j)<>Affine.identity).
Proof. apply filter_correct. Qed.

Lemma decoded_ok : exists dk,decoder_image dk /\ decoded_result dk.
Proof.
 destruct decoder_certificate as [dk [Image Decoder]];exists dk;split;[exact Image|].
 intros b flat ptr q pad init len out Bytes Pad Pos Made m os.
 destruct(observed _ _ Made) as [Q Tables].
 assert (K:FieldOps.checked code=true) by (vm_compute;reflexivity).
 destruct(direct_correct dk code flat ptr q (product b) (eligible m) pad init Decoder K Bytes Pad Q)
 as [mask [Run Bits]]. exists mask;split;[exact Run|]. split.
 - apply scatter_lanes;[exact Pos|reflexivity].
 - intros j J;rewrite andb_true_iff,(Bits j J). unfold accepts.
   change (eligible m j=true) with (eligible(filtered b) j=true).
   rewrite filtered_ok by assumption;tauto.
Qed.

Lemma flush_verified : exists k,exact_image k /\ flush_result k.
Proof.
 destruct flush_ok as [k [Image Run]]. exists k;split;[exact Image|].
 intros n flat pts enc jobs pad init len out N Layout Bytes Pad Inputs meta.
 assert (C:forall i,(i<n)%nat -> valid_chunk(point_words flat pts i)(product(jobs i)) /\ positions(meta i) len).
 { intros i I;destruct(Inputs i I) as [M P];split;[apply observed;exact M|exact P]. }
 destruct(Run n flat pts enc (fun i=>product(jobs i)) pad init meta len out N Layout Bytes Pad C)
 as [bits [E Bits]]. exists bits;split;[exact E|]. intros i j I J.
 rewrite andb_true_iff,(Bits i j I J). unfold accepts,meta.
 destruct(Inputs i I) as [M _];destruct(observed _ _ M) as [_ Tables].
 rewrite filtered_ok by assumption;tauto.
Qed.

Lemma push_verified : push_result.
Proof.
 intros b flat ptr n pad len out B N P Pos m;split;[apply dispatch_ok;assumption|].
 intro Skip;split.
 - apply scatter_lanes;[exact Pos|intros;apply Z.bits_0].
 - intros j J [_ [_ [Enc Strong]]];apply Strong;exact(screen_sound flat ptr B Skip j J _ Enc).
Qed.

Theorem assembled_dalek_post_hash_correct : dalek_post_hash_contract.
Proof.
 constructor.
 - split.
   + intros s H;destruct s;try (simpl in H;intuition discriminate);vm_compute;split;reflexivity.
   + vm_compute;repeat split;reflexivity.
 - vm_compute;repeat split;reflexivity.
 - exact (conj (candidate_abi_ok false) push_abi_ok).
 - split;[intros [] [];repeat split;reflexivity|repeat split;reflexivity].
 - intros b slide Inputs Handoff.
   destruct (product_returns false slide _ _ _ _ Inputs Handoff) as [mid [q [ip Run]]].
   exists q, slide, mid, ip; exact Run.
 - exact filtered_ok.
 - exact push_verified.
 - exact flush_verified.
 - exact decoded_ok.
Qed.
