From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.ScalarBytes execution.LinkedRun execution.MappedFetch memory.MemoryGeometry memory.ByteMemory.
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
Definition post_with (values:FlatMemory.bytes->Prop) entry e r := accounted e (writable e) (at_end r) /\ (regs(machine(at_end r)) 0%nat=1 /\ values (mem(machine(at_end r)))) /\ byte_memory(mem(machine(at_end r))) /\
 match r with
 | BatchReturned q=>(Scatter.count e<=8)%nat /\ ip q=read_word (mem e) (sp e) /\ regs(machine q) 4%nat=sp e+8 /\ RejectFinish.callee_saved e (machine q)
 | NextChunk q=>(8<Scatter.count e)%nat /\ ip q=entry+offset Choose /\ regs(machine q) 4%nat=Rows.frame e /\
   regs(machine q) 12%nat=Z.of_nat (Scatter.count e-8) /\ carry q=Some false /\ StageEntry.saved_caller e (machine q)
 end.
Definition zero_results e (m:FlatMemory.bytes):=forall j,(j<Nat.min (Scatter.count e) 8)%nat ->
 m(output e+Z.of_nat(Scatter.position e j))=0.
Definition post entry e r:=post_with (zero_results e) entry e r.
Lemma post_map (before after:FlatMemory.bytes->Prop) entry e r : (forall m,before m -> after m) ->
 post_with before entry e r -> post_with after entry e r.
Proof. intros F [Paid [[OK Data] Rest]];split;[exact Paid|split;[split;[exact OK|now apply F]|exact Rest]]. Qed.

Lemma classified_with (values:FlatMemory.bytes->Prop) entry e p q : placement e ->
 regs(machine p) 12%nat=Prologue.rows_left (regs e 6%nat) ->
 RejectFinish.post entry e p q -> (regs(machine p) 0%nat=1 /\ values(mem(machine p))) -> byte_memory(mem(machine p)) -> post_with values entry e (classify p q).
Proof.
 intros Place Left [A [_ [Mem [Status Exit]]]] [OK Zeros] Bytes.
 assert (Outputs:regs(machine q) 0%nat=1 /\ values(mem(machine q))) by (now rewrite Status,Mem).
 assert (Octets:byte_memory(mem(machine q))) by (now rewrite Mem).
 assert (Small:RejectFinish.stopping p=true -> (Scatter.count e<=8)%nat).
 { unfold stopping;rewrite OK,Left;change ((word (Prologue.rows_left (regs e 6%nat))=?0)=true -> (Scatter.count e<=8)%nat).
   pose proof(proj1(initial_cpu _ Place) 6%nat) as Fit;unfold Prologue.rows_left,Scatter.count.
   rewrite (word_fits _ Fit);destruct (Z.ltb_spec (regs e 6%nat) 8);[lia|].
   rewrite (word_fits (regs e 6%nat-8)),(word_fits (regs e 6%nat-8)) by (unfold word64 in *;lia).
   intro Z;apply Z.eqb_eq in Z;lia. }
 unfold classify;destruct(RejectFinish.stopping p) eqn:Stop;
   [exact (conj A (conj Outputs (conj Octets (conj (Small eq_refl) Exit))))|].
 unfold stopping in Stop;apply Bool.orb_false_iff in Stop as [_ More].
 rewrite Left in More;pose proof(proj1(initial_cpu _ Place) 6%nat) as N.
 assert (Count:Z.of_nat(Scatter.count e)=regs e 6%nat) by (unfold Scatter.count;apply Z2Nat.id,N).
 assert (Long:8<regs e 6%nat).
 { unfold Prologue.rows_left in More;rewrite (word_fits _ N) in More.
   destruct(Z.ltb_spec (regs e 6%nat) 8);[discriminate|].
   destruct(Z.eq_dec (regs e 6%nat) 8) as [F|];[rewrite F in More;discriminate|lia]. }
 destruct Exit as [PC [SP [CPU [CF Saved]]]].
 split;[exact A|split;[exact Outputs|split;[exact Octets|split;[lia|split;[exact PC|split;[exact SP|]]]]]].
 split;[|exact(conj CF Saved)];rewrite CPU;change (regs(machine p) 12%nat=Z.of_nat(Scatter.count e-8)).
 rewrite Left;unfold Prologue.rows_left;rewrite (word_fits _ N),(proj2(Z.ltb_ge (regs e 6%nat) 8) ltac:(lia)),word_fits by (unfold word64 in *;lia);lia.
Qed.
Lemma classified entry e p q : placement e ->
 regs(machine p) 12%nat=Prologue.rows_left (regs e 6%nat) ->
 RejectFinish.post entry e p q -> RejectOutputs.outputs e (machine p) -> byte_memory(mem(machine p)) -> post entry e (classify p q).
Proof. exact (classified_with (zero_results e) entry e p q). Qed.

Theorem finish_checked pol bias pc text e q :
 RejectDispatch.bound pc text -> RejectFinish.bound text -> placement e -> LoadedImage.loaded pol bias (mem e) (writable e) ->
 fits64 (bias+pc) (Z.of_nat(length text)) -> offset Continue<Z.of_nat(length text) ->
 mapped (mem e) (bias+pc) text -> (forall x,bias+pc<=x<bias+pc+Z.of_nat(length text)->~writable e x) ->
 (0<Scatter.count e)%nat -> Scatter.indices e -> accounted e (writable e) q ->
 ip q=word(bias+pc+offset Prepared) -> regs(machine q) 4%nat=Rows.frame e -> Prologue.output_registers e (machine q) ->
 regs(machine q) 12%nat=Prologue.rows_left (regs e 6%nat) -> regs(machine q) 0%nat mod 2^32=0 ->
 StageEntry.metadata e (mem(machine q)) -> StageEntry.saved_caller e (machine q) -> byte_memory(mem(machine q)) ->
 exists r,finish_chunk bias pc text q=Some r /\ post (bias+pc) e r.
Proof.
 intros Code Exit P I Range Len Map Apart N Idx Paid PC SP Args Left Zero Meta Saved Bytes.
 destruct(RejectDispatch.resume pol bias pc text e q Code P I Range Len Map Apart Paid PC SP Args Left Zero N Idx Meta Saved Bytes)
   as [cont [Dispatch [Continued [Stored [Kept Octets]]]]].
 destruct(RejectFinish.next _ _ _ _ _ Exit P Map Apart Continued Kept) as [last [End Result]].
 exists(classify cont last);split;[unfold finish_chunk;rewrite Dispatch;cbn [bind];now rewrite End|].
 apply classified with (p:=cont) (q:=last);[exact P|exact (proj2(proj2(proj2 Continued)))|exact Result|exact Stored|exact Octets].
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
