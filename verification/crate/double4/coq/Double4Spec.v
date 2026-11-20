From Coq Require Import List ZArith Lia Ring.
From Curve25519 Require Export Field Radix51 Edwards.
From Ed25519Simd Require Export Wide51.
Import ListNotations. Open Scope Z_scope.

(* The arithmetic guarantee is conditional on the three coordinate bounds.
   The public theorem separately guarantees memory/ABI safety for any qwords. *)
Definition double4_spec before after := loose_xyz before ->
 forall j c, (j<8)%nat -> (c<4)%nat ->
 reduced (fun i => cell after (5*c+i)%nat j) /\
 field_at after (5*c)%nat j mod prime =
 coordinate (double_n 4 (point_values before j)) c mod prime.
Lemma spec_ext before after before' after' :
 (forall k,(k<160)%nat ->before' k=before k) ->
 (forall k,(k<160)%nat ->after' k=after k) ->
 double4_spec before after -> double4_spec before' after'.
Proof.
 intros In Out Spec Bound j c J C.
 assert(B:loose_xyz before).
 { intros coord lane CI LI;apply(loose_ext (fun i=>cell before'(5*coord+i)%nat lane));[|apply Bound;assumption].
   intros i I;unfold cell;apply In;lia. }
 destruct(Spec B j c J C)as[Bounds V];split.
 - intros i I;unfold cell;rewrite Out by lia;apply Bounds;exact I.
 - rewrite(field_at_ext after' after)by (auto;lia);rewrite(point_values_ext before' before)by (auto;lia);exact V.
Qed.
