From Coq Require Import List ZArith Lia.
From Machine Require execution.Composition.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Ed25519Simd.VerifyBatch Require Import Policy Return Image Audit Iteration ChunkDispatch.
From Ed25519Simd.VerifyBatch Require TableCertificate StrictAccept.
Local Open Scope Z_scope.
Section Iteration.
Context `{iteration:BatchWindow.t}.

Definition result pol bias pc e:=RejectExecution.post_with (ScoredChunk.outputs pol e) (bias+pc) e.

Lemma publish_checked pol bias pc text e h digest caller started screen:admissible pol bias pc text e ->
 matches pc (destination pol) text -> StrictDispatch.bound pc text -> (0<BatchWindow.remaining e)%nat ->
 HashLayout.active pol e -> ScoreStart.reached pol bias pc e h digest caller started ->
 ScoreProgress.observed pol bias started screen ->
 (exists last,publish pol bias pc text screen last) /\
 forall last,publish pol bias pc text screen last -> result pol bias pc e last.
Proof.
 intros A M Bound N Live Ready Progress;pose proof (BatchWindow.total e N) as Total.
 assert (Full:(0<Scatter.count e)%nat) by lia.
 destruct(batch_inputs _ _ _ _ _ A Full) as [P [_ [[Range Sep] [Maps [Idx Entries]]]]].
 pose proof(callee_image _ _ _ _ _ A Full) as I;pose proof(entry_text _ _ _ _ _ A) as Map.
 pose proof(proj2(proj2(proj2(Entries BatchWindow.first (BatchWindow.remaining e) N Total)))) as Geo.
 unfold publish;destruct(ScoreProduct.rejected pol screen) eqn:Zero.
 - destruct pol;[discriminate|]. change ((regs(machine screen) 12%nat=?0)=true) in Zero;apply Z.eqb_eq in Zero.
   destruct(proj2(StrictScreen.with_frame _ _ _ _ _ _ _ P I Live Ready) _ Progress) as [Decision Frame].
   destruct(@ScorePublish.checked iteration _ _ _ _ _ _ _ M Bound P I Range Map Sep N Idx Decision Frame Zero)
      as [v [Run Post]];split;[exists v;exact Run|].
   intros last Eq;rewrite Run in Eq;injection Eq as <-;unfold result;eapply RejectExecution.post_map;[|exact Post].
   intros m Z;apply zeros;[|exact Z]. intros j J Row Sig;pose proof(StrictScreen.lane _ _ _ Decision j J) as B;rewrite Zero,Z.bits_0 in B.
   enough (StrictOrderClear.eligible e j) by (apply (proj2 B) in H;discriminate).
   apply StrictAccept.screened;unfold HashLayout.row;now rewrite BatchWindow.own_row by exact Row.
 - eapply Composition.sequence.
   + exact (ScoreDecision.checked _ _ _ _ _ _ _ _ _ P I Geo Maps (Tables.loaded _ _ TableCertificate.static_tables_correct Maps) Live Ready Progress Zero).
   + intros p [_ [prod [_ Decision]]].
     assert (Both:exists t mask,ScoreTail.entry bias pc e t p mask /\ ScoredChunk.verdict pol e p mask)
       by (destruct pol;[exact(ScoredChunk.zip _ _ _ _ Decision)|exact Decision]).
     destruct Both as [t [mask [C V]]]. apply Composition.option_result.
     exact (@ScoredChunk.publish iteration pol bias pc _ text e t p mask M Bound P I Range Map Sep N Idx C V).
Qed.

Theorem checked pol bias pc text e h digest:admissible pol bias pc text e -> matches pc (destination pol) text ->
 StrictDispatch.bound pc text -> ScoreSetup.bound pol pc text -> (0<BatchWindow.remaining e)%nat ->
 ChunkDispatch.post pol bias pc e (FirstDispatch.HashReturned h digest) ->
 (exists last,score pol bias pc text h digest last) /\
 forall last,score pol bias pc text h digest last -> result pol bias pc e last.
Proof.
 intros A M B Code N [Live [Ret [Inputs Words]]];pose proof(BatchWindow.total e N) as Total.
 assert(Full:(0<Scatter.count e)%nat) by lia;destruct(batch_inputs _ _ _ _ _ A Full) as [P [_ [[Range Sep] [_ [_ Entries]]]]].
 pose proof(callee_image _ _ _ _ _ A Full) as I;pose proof(entry_text _ _ _ _ _ A) as Map.
 pose proof(proj2(proj2(proj2(Entries BatchWindow.first (BatchWindow.remaining e) N Total)))) as Geo.
 unfold score. eapply Composition.sequence.
 - exact (ScoreStart.from_hash_checked _ _ _ _ _ _ _ Code P I Range Map Sep Inputs Ret Words).
 - intros started [child Ready]. eapply Composition.sequence.
   + apply Composition.observations. exact (proj1 (ScoreProgress.checked _ _ _ _ _ _ _ _ P I Geo Live Ready)).
   + intros screen Progress. exact (publish_checked _ _ _ _ _ _ _ _ _ _ A M B N Live Ready Progress).
Qed.
End Iteration.
