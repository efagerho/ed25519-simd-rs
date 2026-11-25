From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Image Return Audit.
From Ed25519Simd.VerifyBatch Require Iteration BatchWindow ChunkBegin ChunkRestart ChunkScore.
Local Open Scope Z_scope.

Section Batch.
Variables (pol:policy) (bias pc:Z) (text:list Z) (e:cpu).
Hypotheses (caller:admissible pol bias pc text e) (image:matches pc (destination pol) text)
 (code:StrictDispatch.bound pc text) (scorer:ScoreSetup.bound pol pc text)
 (restart:ChunkRestart.code text (destination pol Prepare-pc)).

Lemma symbol : destination pol Prepare=BatchScalar.first_symbol pol.
Proof. destruct pol;reflexivity. Qed.

Section Window.
Context `{iteration:BatchWindow.t}.
Variables (p:cursor) (masks:nat->nat->bool).
Hypotheses (live:(0<BatchWindow.remaining e)%nat)
 (earlier:forall x,BatchWindow.earlier e x -> mem(machine p) x=BatchWindow.before x)
 (staged:ChunkStaging.entry (bias+pc) (destination pol Prepare-pc) e BatchWindow.first (BatchWindow.remaining e) p).

Lemma step: (exists last,Iteration.observed pol bias pc text e p masks last) /\
 forall last,Iteration.observed pol bias pc text e p masks last -> ChunkScore.result pol bias pc e last.
Proof.
 pose proof staged as St;rewrite symbol in St.
 destruct(ChunkDispatch.checked pol bias pc text e p masks caller code live St earlier) as [b [Run Post]].
 assert (Finish:(exists r,Iteration.finish pol bias pc text b r) /\
   forall r,Iteration.finish pol bias pc text b r -> ChunkScore.result pol bias pc e r).
 { destruct b as [q|q|h d];[split;[eexists;reflexivity|intros r ->;exact Post]|
     split;[eexists;reflexivity|intros r ->;exact Post]|exact(ChunkScore.checked _ _ _ _ _ _ _ caller image code scorer live Post)]. }
 split;[destruct(proj1 Finish) as [r R];exists r,b;auto|].
 intros r [v [V End]];rewrite Run in V;injection V as <-;exact(proj2 Finish r End).
Qed.
End Window.

Lemma step_at first n p masks:(0<n)%nat -> (first+n=Scatter.count e)%nat ->
 ChunkStaging.entry (bias+pc) (destination pol Prepare-pc) e first n p ->
 (exists last,Iteration.observed pol bias pc text e p masks last) /\ forall last,
 Iteration.observed pol bias pc text e p masks last -> @ChunkScore.result (BatchWindow.at_memory first (mem(machine p))) pol bias pc e last.
Proof.
 intros Live Total St;set(w:=BatchWindow.at_memory first (mem(machine p))).
 assert (N:@BatchWindow.remaining w e=n) by (rewrite BatchWindow.rest;change (Scatter.count e-first=n)%nat;lia).
 exact(@step w p masks ltac:(now rewrite N) ltac:(intros;reflexivity) ltac:(rewrite N;exact St)).
Qed.

Lemma advance first n p q:(first+n=Scatter.count e)%nat ->
 @ChunkScore.result (BatchWindow.at_memory first (mem(machine p))) pol bias pc e (RejectExecution.NextChunk q) ->
 (8<n)%nat /\ exists next,ChunkStaging.execute (bias+pc) text (n-8) q=Some next /\
      ChunkStaging.entry (bias+pc) (destination pol Prepare-pc) e (first+8) (n-8) next /\
      preserved (BatchWindow.output_byte e) (mem(machine q)) (mem(machine next)).
Proof.
 intros Total Post;set(w:=BatchWindow.at_memory first (mem(machine p))).
 assert (N:@BatchWindow.remaining w e=n) by (rewrite BatchWindow.rest;change (Scatter.count e-first=n)%nat;lia).
 pose proof Post as [_ [_ [_ [Long _]]]];change (8<@BatchWindow.remaining w e)%nat in Long;rewrite N in Long;split;[exact Long|].
 destruct(batch_inputs _ _ _ _ _ caller ltac:(lia)) as [P [[Read _] [[_ Sep] _]]].
 rewrite <-N;destruct(@ChunkRestart.checked_frame w (bias+pc) text _ e q _ restart P Read (entry_text _ _ _ _ _ caller) Sep Post) as [v [Run [Entry Frame]]];exists v;auto.
Qed.

Lemma progress n : forall first p masks,(0<n)%nat -> (first+n=Scatter.count e)%nat ->
 ChunkStaging.entry (bias+pc) (destination pol Prepare-pc) e first n p ->
 exists last,Iteration.chain pol bias pc text e n p masks last.
Proof.
 induction n using lt_wf_ind;intros first p masks Live Total St.
 destruct(step_at first n p masks Live Total St) as [[[q|q] Run] All].
 - exists q;apply Iteration.done,Run.
 - destruct(advance first n p q Total (All _ Run)) as [Long [v [G [Entry _]]]].
   destruct(H (n-8)%nat ltac:(lia) (first+8)%nat v masks ltac:(lia) ltac:(lia) Entry) as [last Tail].
   exists last;eapply Iteration.more;eassumption.
Qed.

Definition prefix_at n m:=Scatter.prefix e pol n (fun j=>m(output e+Z.of_nat j)).

Lemma append_window first n p q:(first+n=Scatter.count e)%nat -> (0<n)%nat ->
 prefix_at first (mem(machine p)) ->
 (forall i,(i<first)%nat -> mem(machine q)(output e+Z.of_nat(Scatter.position e i))=
    mem(machine p)(output e+Z.of_nat(Scatter.position e i))) ->
 @ScoredChunk.outputs (BatchWindow.at_memory first (mem(machine p))) pol e (mem(machine q)) ->
 prefix_at (first+Nat.min n 8) (mem(machine q)).
Proof.
 intros T N Old Same New i I;destruct (lt_dec i first) as [Earlier|Current].
 - rewrite Same by exact Earlier;apply Old,Earlier.
 - set(w:=BatchWindow.at_memory first (mem(machine p))) in *.
   assert (J:(i-first<Nat.min (@BatchWindow.remaining w e) 8)%nat)
     by (rewrite BatchWindow.rest;change (i-first<Nat.min (Scatter.count e-first) 8)%nat;lia).
   specialize(New (i-first)%nat J);change (@BatchWindow.first w) with first in New.
   now replace (first+(i-first))%nat with i in New by lia.
Qed.

Lemma sound n p masks last:Iteration.chain pol bias pc text e n p masks last ->
 forall first,(0<n)%nat -> (first+n=Scatter.count e)%nat ->
 ChunkStaging.entry (bias+pc) (destination pol Prepare-pc) e first n p ->
 prefix_at first (mem(machine p)) ->
 Iteration.exit e last /\ prefix_at (Scatter.count e) (mem(machine last)).
Proof.
 induction 1 as [n p masks last Run|n p masks back next k last Run G Tail IH];intros first Live Total St Old;
   pose proof(proj2(step_at first n p masks Live Total St) _ Run) as Post;
   destruct(batch_inputs _ _ _ _ _ caller ltac:(lia)) as [P [_ [_ [_ [Idx _]]]]];
   set(w:=BatchWindow.at_memory first (mem(machine p))) in *;
   assert (N:@BatchWindow.remaining w e=n) by (rewrite BatchWindow.rest;change (Scatter.count e-first=n)%nat;lia).
 - destruct Post as [Paid [[OK Current] [Bytes [Small End]]]].
   pose proof (@RejectExecution.end_abi w _ _ _ End) as ABI.
   split;[exact(conj Paid (conj Bytes (conj OK ABI)))|].
   change (@BatchWindow.remaining w e<=8)%nat in Small;rewrite N in Small.
   replace (Scatter.count e) with (first+Nat.min n 8)%nat by lia.
   apply (append_window first n p last Total Live Old);[|exact Current].
   destruct first as [|first];[intros;lia|].
   destruct End as [_ Saved];apply (@BatchWindow.previous w e _ P Idx ltac:(change (S first<=Scatter.count e)%nat;lia) Saved).
 - destruct(advance first n p back Total Post) as [Long [v [V [Entry Frame]]]];rewrite G in V;injection V as <-.
   apply(IH (first+8)%nat ltac:(lia) ltac:(lia) Entry).
   destruct Post as [_ [[_ Current] [_ [_ [_ [_ [_ [_ [[Saved _] _]]]]]]]]].
   pose proof(append_window first n p back Total Live Old
      (@BatchWindow.previous w e _ P Idx ltac:(change (first<=Scatter.count e)%nat;lia) Saved) Current) as Published.
   intros i I;rewrite Frame;[apply Published;lia|].
   specialize(proj1 Idx i ltac:(lia)) as Bound;unfold BatchWindow.output_byte,span;lia.
Qed.

Theorem checked_verdicts cf masks:(0<Scatter.count e)%nat ->
 StageEntry.physical (bias+pc) text (destination pol Prepare-pc) e ->
 (exists last,Iteration.native pol bias pc text e cf masks last) /\
 forall last,Iteration.native pol bias pc text e cf masks last -> Iteration.exit e last /\ prefix_at (Scatter.count e) (mem(machine last)).
Proof.
 intros N Enter;destruct(batch_inputs _ _ _ _ _ caller N) as [P [[Read _] _]].
 destruct(ChunkBegin.checked _ _ _ _ cf P Read Enter) as [p [Run St]].
 destruct(progress (Scatter.count e) 0%nat p masks N eq_refl St) as [last Steps].
 split;[exists last,p;auto|intros q [v [Start R]];rewrite Run in Start;injection Start as <-;exact (sound _ _ _ _ R 0%nat N eq_refl St ltac:(intros i I;lia))].
Qed.
End Batch.
