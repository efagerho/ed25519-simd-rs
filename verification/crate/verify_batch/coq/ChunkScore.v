From Coq Require Import List ZArith Lia.
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
 pose proof(proj2(proj2(proj2(proj2(Entries BatchWindow.first (BatchWindow.remaining e) Loop.zero_loc N Total Loop.zero_words))))) as Geo.
 unfold publish;destruct(ScoreProduct.rejected pol screen) eqn:Zero.
 - destruct pol;[discriminate|]. change ((regs(machine screen) 12%nat=?0)=true) in Zero;apply Z.eqb_eq in Zero.
   destruct(proj2(StrictScreen.with_frame _ _ _ _ _ _ _ P I Live Ready) _ Progress) as [Decision Frame].
   destruct(@ScorePublish.checked iteration _ _ _ _ _ _ _ M Bound P I Range Map Sep N Idx Decision Frame Zero)
      as [v [Run Post]];split;[exists v;exact Run|].
   intros last Eq;rewrite Run in Eq;injection Eq as <-;unfold result;eapply RejectExecution.post_map;[|exact Post].
   intros m Z;apply zeros;[|exact Z]. intros j J Row Sig;pose proof(StrictScreen.lane _ _ _ Decision j J) as B;rewrite Zero,Z.bits_0 in B.
   enough (StrictOrderClear.eligible e j) by (apply (proj2 B) in H;discriminate).
   apply StrictAccept.screened;unfold HashLayout.row;now rewrite BatchWindow.own_row by exact Row.
 - destruct(ScoreDecision.checked _ _ _ _ _ _ _ _ _ P I Geo Maps (Tables.loaded _ _ TableCertificate.static_tables_correct Maps) Live Ready Progress Zero)
      as [[q Found] All].
   assert (End:forall q,ScoreDecision.observed pol bias screen q -> exists r,ScorePublish.scatter bias pc text q=Some r /\ result pol bias pc e r).
   { intros p Run;destruct (All p Run) as [_ [prod [_ Decision]]].
     assert (Both:exists t mask,ScoreTail.entry bias pc e t p mask /\ ScoredChunk.verdict pol e p mask)
       by (destruct pol;[exact(ScoredChunk.zip _ _ _ _ Decision)|exact Decision]).
     destruct Both as [t [mask [C V]]];exact (@ScoredChunk.publish iteration pol bias pc _ text e t p mask M Bound P I Range Map Sep N Idx C V). }
   split;[destruct(End q Found) as [v [Run _]];exists v,q;auto|].
   intros v [s [R Finish]];destruct(End s R) as [u [Run Q]];rewrite Finish in Run;now injection Run as <-.
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
 pose proof(proj2(proj2(proj2(proj2(Entries BatchWindow.first (BatchWindow.remaining e) Loop.zero_loc N Total Loop.zero_words))))) as Geo.
 assert (Call:forall s cf,HashResume.compatible digest s -> well_formed s ->
    exists child,ScoreCall.execute bias pc text h digest s cf=Some child /\ ScoreCall.entered pol bias pc e h digest child).
 { intros s cf C W;apply ScoreCall.checked;assumption. }
 split.
 - destruct(HashResume.complete_ok _ _ _ _ _ _ e P Words (initial_cpu _ P) Ret) as [C W].
   destruct(Call _ (carry h) C W) as [child [H Child]];destruct(ScoreStart.from_entry _ _ _ _ _ _ _ P I Child) as [v [Start Ready]].
   destruct(proj1(ScoreProgress.checked _ _ _ _ _ _ _ _ P I Geo Live Ready)) as [screen Run].
   destruct(proj1(publish_checked _ _ _ _ _ _ _ _ _ _ A M B N Live Ready Run)) as [last Last].
   exists last,(HashResume.complete digest e),(carry h),child,v,screen;split;[exact C|split;[exact W|split;[exact H|split;[exact Start|exact (conj Run Last)]]]].
 - intros last [s [cf [child [v [screen [C [W [H [Run [S End]]]]]]]]]].
   destruct(Call s cf C W) as [c [R Child]];rewrite H in R;injection R as <-.
   destruct(ScoreStart.from_entry _ _ _ _ _ _ _ P I Child) as [u [Start Ready]];rewrite Run in Start;injection Start as <-.
   exact (proj2(publish_checked _ _ _ _ _ _ _ _ _ _ A M B N Live Ready S) last End).
Qed.
End Iteration.
