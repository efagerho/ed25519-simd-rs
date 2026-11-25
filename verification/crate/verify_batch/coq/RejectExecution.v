From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.ScalarBytes execution.LinkedRun memory.ByteMemory.
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
Definition post entry e r := accounted e (writable e) (at_end r) /\ RejectOutputs.outputs e (machine(at_end r)) /\ byte_memory(mem(machine(at_end r))) /\
 match r with
 | BatchReturned q=>(Scatter.count e<=8)%nat /\ ip q=read_word (mem e) (sp e) /\ regs(machine q) 4%nat=sp e+8 /\ RejectFinish.callee_saved e (machine q)
 | NextChunk q=>(8<Scatter.count e)%nat /\ ip q=entry+offset Choose /\ regs(machine q) 4%nat=Rows.frame e
 end.
Lemma classified entry e p q : placement e ->
 regs(machine p) 12%nat=Prologue.rows_left (regs e 6%nat) ->
 RejectFinish.post entry e p q -> RejectOutputs.outputs e (machine p) -> byte_memory(mem(machine p)) -> post entry e (classify p q).
Proof.
 intros Place Left [A [_ [Mem [Status Exit]]]] [OK Zeros] Bytes.
 assert (Outputs:RejectOutputs.outputs e (machine q)) by
   (split;[now rewrite Status|intros j J;rewrite Mem;apply Zeros,J]).
 assert (Octets:byte_memory(mem(machine q))) by (now rewrite Mem).
 assert (Small:RejectFinish.stopping p=true -> (Scatter.count e<=8)%nat).
 { unfold stopping;rewrite OK,Left;change ((word (Prologue.rows_left (regs e 6%nat))=?0)=true -> (Scatter.count e<=8)%nat).
   pose proof(proj1(initial_cpu _ Place) 6%nat) as Fit;unfold Prologue.rows_left,Scatter.count.
   rewrite (word_fits _ Fit);destruct (Z.ltb_spec (regs e 6%nat) 8);[lia|].
   rewrite (word_fits (regs e 6%nat-8)),(word_fits (regs e 6%nat-8)) by (unfold word64 in *;lia).
   intro Z;apply Z.eqb_eq in Z;lia. }
 unfold classify;destruct(RejectFinish.stopping p) eqn:Stop;
   [exact (conj A (conj Outputs (conj Octets (conj (Small eq_refl) Exit))))|split;[exact A|split;[exact Outputs|split;[exact Octets|split;[|exact Exit]]]]].
 unfold stopping in Stop;apply Bool.orb_false_iff in Stop as [_ More].
 rewrite Left in More;unfold Prologue.rows_left in More.
 pose proof(proj1(initial_cpu _ Place) 6%nat) as N.
 rewrite (word_fits _ N) in More;destruct(regs e 6%nat <? 8) eqn:Less;[discriminate|].
 apply Z.ltb_ge in Less;unfold Scatter.count;destruct (Z.eq_dec (regs e 6%nat) 8) as [Full|NotFull];
   [rewrite Full in More;discriminate|lia].
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
