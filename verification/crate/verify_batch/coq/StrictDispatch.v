From Coq Require Import List ZArith Lia.
From Machine Require Import execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.MappedFetch memory.MemoryGeometry memory.ByteMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Image Return LoadedImage.
From Ed25519Simd.VerifyBatch Require StrictReturn HashEntry RejectExecution.
Local Open Scope Z_scope.

(* Rejoin the batch wrapper at its TEST EAX. Its two paths either scatter
   zeros and exit the round, or pass the filtered lengths to SHA. *)
Definition bound pc text:=HashEntry.bound pc text /\ RejectDispatch.bound pc text /\
 RejectFinish.bound text /\ offset Continue<Z.of_nat(length text).
Inductive outcome:=Zero (r:RejectExecution.outcome) | HashCall (q:cursor).
Definition endpoint v:=match v with Zero r=>RejectExecution.at_end r | HashCall q=>q end.
Definition execute bias pc text q ks:=if regs(machine q) 0%nat mod 2^32=?0
 then option_map Zero (RejectExecution.finish_chunk bias pc text q)
 else option_map (fun v=>HashCall (fst v)) (HashEntry.execute bias pc text q ks).
Record reached bias pc e p q v:Prop:=Reached {
 preparation:StrictReturn.result (bias+pc) e p q;
 branch:match v with
 | Zero r=>~StrictReturn.live e (machine p) /\ RejectExecution.post (bias+pc) e r
 | HashCall h=>StrictReturn.live e (machine p) /\ HashEntry.entry bias pc e q h end
}.
Lemma accounted_end bias pc e p q v : reached bias pc e p q v -> accounted e (writable e) (endpoint v).
Proof. intros [_ B];destruct v as [r|h];[exact (proj1(proj2 B))|exact (HashEntry.writes _ _ _ _ _ (proj2 B))]. Qed.

Theorem checked bias pc text e p q ks : bound pc text -> placement e -> loaded Dalek bias (mem e) (writable e) ->
 fits64 (bias+pc) (Z.of_nat(length text)) -> mapped (mem e) (bias+pc) text ->
 (forall x,bias+pc<=x<bias+pc+Z.of_nat(length text)->~writable e x) ->
 (0<Scatter.count e)%nat -> Scatter.indices e ->
 StrictReturn.result (bias+pc) e p q -> exists v,execute bias pc text q ks=Some v /\ reached bias pc e p q v.
Proof.
 intros [Hash [Scatter [Exit Len]]] P I Fit Map Apart N Idx Q.
 destruct(StrictReturn.decision _ _ _ _ Q) as [[ZeroAX|One] Live];unfold execute.
 - rewrite ZeroAX;change (0 mod 2^32=?0) with true.
   destruct(RejectExecution.finish_checked Dalek bias pc text e q Scatter Exit P I Fit Len Map Apart N Idx (StrictReturn.writes _ _ _ _ Q)
     (StrictReturn.pc _ _ _ _ Q) (StrictReturn.stack _ _ _ _ Q) (StrictReturn.outputs _ _ _ _ Q) (StrictReturn.remaining _ _ _ _ Q)
     ltac:(now rewrite ZeroAX) (StrictReturn.metadata _ _ _ _ Q) (StrictReturn.saved _ _ _ _ Q) (proj2(proj2(StrictReturn.words _ _ _ _ Q))))
     as [r [Run R]].
   exists (Zero r);split;[now rewrite Run|constructor;[exact Q|split;[intro H;apply Live in H;lia|exact R]]].
 - rewrite One;change (1 mod 2^32=?0) with false.
   assert (PC:ip q=bias+pc+385).
   { rewrite (StrictReturn.pc _ _ _ _ Q);apply word_fits;destruct Fit;change (574<Z.of_nat(length text)) in Len;unfold word64;lia. }
   destruct(HashEntry.checked Dalek bias pc text e q ks Hash P I Fit Map Apart PC One (StrictReturn.stack _ _ _ _ Q)
      (StrictReturn.scratch_reg _ _ _ _ Q) (StrictReturn.writes _ _ _ _ Q) (StrictReturn.words _ _ _ _ Q) (StrictReturn.inputs _ _ _ _ Q))
    as [h [k [Run H]]].
   exists (HashCall h);split;[now rewrite Run|constructor;[exact Q|split;[apply Live,One|exact H]]].
Qed.
