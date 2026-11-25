From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.ScalarBytes execution.ScalarWords execution.LinkedRun execution.MappedFetch memory.MemoryGeometry memory.ByteMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Rows Image Return BatchScalar PrepareUnwind RejectDispatch RejectFinish.
Local Open Scope Z_scope.

Inductive outcome := BatchReturned (p:cursor) | NextChunk (p:cursor).
Definition at_end r := match r with BatchReturned p | NextChunk p=>p end.
Definition classify p q := if RejectFinish.stopping p then BatchReturned q else NextChunk q.
Definition finish_chunk bias pc text caller :=
 bind (RejectDispatch.scatter_stores bias pc text caller) (fun cont=>
 option_map (classify cont) (RejectFinish.leave (bias+pc) text cont)).
Definition scalar_rejection pol bias pc text e c masks :=
 bind (BatchScalar.observe pol bias (bias+pc) text e c masks) (fun scalar=>
 if regs(machine scalar) 0%nat mod 2^32=?0 then
 bind (PrepareUnwind.unwind pol bias scalar) (finish_chunk bias pc text)
 else None).
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition final_frame e m (abi:Prop):=match BatchWindow.first with O=>abi | S _=>abi /\ BatchWindow.saved e m end.
Lemma end_with e m (abi:Prop):abi -> BatchWindow.saved e m -> final_frame e m abi.
Proof. unfold final_frame;destruct BatchWindow.first;auto. Qed.
Lemma end_abi e m abi:final_frame e m abi -> abi.
Proof. unfold final_frame;destruct BatchWindow.first;tauto. Qed.
Definition post_with (values:FlatMemory.bytes->Prop) entry e r := accounted e (writable e) (at_end r) /\ (regs(machine(at_end r)) 0%nat=1 /\ values (mem(machine(at_end r)))) /\ byte_memory(mem(machine(at_end r))) /\
 match r with
 | BatchReturned q=>(BatchWindow.remaining e<=8)%nat /\ final_frame e (mem(machine q)) (ip q=read_word (mem e) (sp e) /\ regs(machine q) 4%nat=sp e+8 /\ RejectFinish.callee_saved e (machine q))
 | NextChunk q=>(8<BatchWindow.remaining e)%nat /\ ip q=entry+offset Choose /\ regs(machine q) 4%nat=Rows.frame e /\
   regs(machine q) 12%nat=Z.of_nat (BatchWindow.remaining e-8) /\ carry q=Some false /\ BatchWindow.saved_caller e (machine q) /\ ChunkContext.bindings e (machine q) /\ well_formed(machine q)
 end.
Definition zero_results e (m:FlatMemory.bytes):=forall j,(j<Nat.min (BatchWindow.remaining e) 8)%nat ->
 m(output e+Z.of_nat(Scatter.position e (BatchWindow.first+j)))=0.
Definition post entry e r:=post_with (zero_results e) entry e r.
Lemma post_map (before after:FlatMemory.bytes->Prop) entry e r : (forall m,before m -> after m) ->
 post_with before entry e r -> post_with after entry e r.
Proof. intros F [Paid [[OK Data] Rest]];split;[exact Paid|split;[split;[exact OK|now apply F]|exact Rest]]. Qed.

Lemma classified_with (values:FlatMemory.bytes->Prop) entry e p q : placement e ->
 regs(machine p) 12%nat=BatchWindow.next_count e ->
 BatchWindow.saved_caller e (machine p) -> ChunkContext.bindings e (machine p) -> RejectFinish.post entry e p q -> (regs(machine p) 0%nat=1 /\ values(mem(machine p))) -> well_formed(machine p) -> post_with values entry e (classify p q).
Proof.
 intros Place Left Keep Bindings [A [_ [Mem [Status Exit]]]] [OK Zeros] Bytes.
 assert (Outputs:regs(machine q) 0%nat=1 /\ values(mem(machine q))) by (now rewrite Status,Mem).
 assert (Octets:byte_memory(mem(machine q))) by (rewrite Mem;exact (proj2(proj2 Bytes))).
 assert (L:regs(machine p) 12%nat=Z.of_nat(BatchWindow.remaining e-8)) by
   (rewrite Left;apply BatchWindow.live_count,(initial_cpu _ Place)).
 assert (Fit:word(regs(machine p) 12%nat)=regs(machine p) 12%nat) by (apply word_fits,Bytes).
 assert (Small:RejectFinish.stopping p=true -> (BatchWindow.remaining e<=8)%nat).
 { unfold stopping;rewrite OK;change ((word(regs(machine p) 12%nat)=?0)=true -> (BatchWindow.remaining e<=8)%nat).
   rewrite Fit,L;rewrite Z.eqb_eq;lia. }
 assert (SavedEnd:BatchWindow.saved e (mem(machine q))) by (rewrite Mem;exact (proj1 Keep)).
 unfold classify;destruct(RejectFinish.stopping p) eqn:Stop;
   [exact (conj A (conj Outputs (conj Octets (conj (Small eq_refl) (end_with _ _ _ Exit SavedEnd)))))|].
 assert (Long:(8<BatchWindow.remaining e)%nat).
 { unfold stopping in Stop;apply Bool.orb_false_iff in Stop as [_ More].
   rewrite Fit,L,Z.eqb_neq in More;lia. }
 destruct Exit as [PC [SP [CPU [CF Saved]]]].
 split;[exact A|split;[exact Outputs|split;[exact Octets|split;[lia|split;[exact PC|split;[exact SP|]]]]]].
 split;[rewrite CPU;exact L|split;[exact CF|split;[rewrite CPU;exact Keep|rewrite CPU;split;[destruct Bindings;constructor;assumption|exact Bytes]]]].
Qed.
Lemma classified entry e p q : placement e ->
 regs(machine p) 12%nat=BatchWindow.next_count e ->
 BatchWindow.saved_caller e (machine p) -> ChunkContext.bindings e (machine p) -> RejectFinish.post entry e p q -> RejectOutputs.outputs e (machine p) -> well_formed(machine p) -> post entry e (classify p q).
Proof. exact (classified_with (zero_results e) entry e p q). Qed.

Theorem finish_checked pol bias pc text e q :
 RejectDispatch.bound pc text -> RejectFinish.bound text -> placement e -> LoadedImage.loaded pol bias (mem e) (writable e) ->
 fits64 (bias+pc) (Z.of_nat(length text)) -> offset Continue<Z.of_nat(length text) ->
 mapped (mem e) (bias+pc) text -> (forall x,bias+pc<=x<bias+pc+Z.of_nat(length text)->~writable e x) ->
 (0<BatchWindow.remaining e)%nat -> Scatter.indices e -> accounted e (writable e) q ->
 ip q=word(bias+pc+offset Prepared) -> regs(machine q) 4%nat=Rows.frame e -> Prologue.output_registers e (machine q) ->
 regs(machine q) 12%nat=BatchWindow.next_count e -> regs(machine q) 0%nat mod 2^32=0 ->
 BatchWindow.metadata e (mem(machine q)) -> BatchWindow.saved_caller e (machine q) -> well_formed(machine q) ->
 ChunkContext.bindings e (machine q) ->
 exists r,finish_chunk bias pc text q=Some r /\ post (bias+pc) e r.
Proof.
 intros Code Exit P I Range Len Map Apart N Idx Paid PC SP Args Left Zero Meta Saved Bytes Bindings.
 destruct(RejectDispatch.resume pol bias pc text e q Code P I Range Len Map Apart Paid PC SP Args Left Zero N Idx Meta Saved (proj2(proj2 Bytes)) Bindings)
   as [cont [Dispatch [Continued [Stored [Kept [Octets B]]]]]].
 assert (Words:well_formed(machine cont)).
 { unfold RejectDispatch.scatter_stores in Dispatch;destruct(segment _ _ _ q) as [child|] eqn:Call;[|discriminate].
   exact(returning_wf _ _ _ _ _ (segment_wf _ _ _ _ _ Bytes Call) Dispatch). }
 destruct(RejectFinish.next _ _ _ _ _ Exit P Map Apart Continued (conj (BatchWindow.raw_saved _ _ (proj1 Kept)) (proj2 Kept))) as [last [End Result]].
 exists(classify cont last);split;[unfold finish_chunk;rewrite Dispatch;cbn [bind];now rewrite End|].
 apply classified with (p:=cont) (q:=last);[exact P|exact (proj2(proj2(proj2 Continued)))|exact Kept|exact B|exact Result|exact Stored|exact Words].
Qed.

Theorem final_bytes pol bias pc text e c masks r :
 scalar_rejection pol bias pc text e c masks=Some r -> replays e (at_end r).
Proof.
 unfold scalar_rejection;destruct (BatchScalar.observe _ _ _ _ _ _ _) as [s|] eqn:Start;[|discriminate].
 cbn [bind];destruct (_=?0);[|discriminate]. pose proof (BatchScalar.observed_memory _ _ _ _ _ _ _ _ Start) as Mem.
 unfold PrepareUnwind.unwind,PrepareUnwind.unwind_at;cbn [PrepareUnwind.unwind_length].
 destruct (segment _ _ 9 s) as [common|] eqn:C;[|discriminate];cbn [bind].
 pose proof (segment_memory _ _ _ _ _ _ Mem C) as Common.
 destruct(leave_strict pol bias common) as [caller|] eqn:Strict;[|discriminate];cbn [bind].
 assert (Current:replays e caller) by
   (destruct pol;[injection Strict as <-;exact Common|eapply segment_memory;[exact Common|exact Strict]]).
 unfold finish_chunk,scatter_stores;destruct(segment _ _ 8 caller) as [scatter|] eqn:Dispatch;[|discriminate];cbn [bind].
 destruct(returning _ _ 88 scatter) as [cont|] eqn:Child;[|discriminate];cbn [bind].
 pose proof(returning_memory _ _ _ _ _ _ (segment_memory _ _ _ _ _ _ Current Dispatch) Child) as A.
 unfold RejectFinish.leave,classify;destruct(stopping cont);
   match goal with |-option_map _ ?run=_ -> _=>destruct run eqn:End;[|discriminate] end;
   intro F;injection F as <-;cbn [at_end];[eapply returning_memory|eapply segment_memory];eassumption.
Qed.
End Iteration.
