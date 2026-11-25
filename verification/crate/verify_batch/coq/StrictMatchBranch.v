From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require StrictMatchState.
Import ListNotations. Local Open Scope Z_scope.
Local Notation pc:=(ScoreSetup.callee Dalek).
Local Notation text:=(ScoreSetup.code Dalek).
Definition gate:list line:=[(389,3%nat,And32 12 0);(392,6%nat,Branch Equal (554-398))].
Definition finish:list line:=[(549,3%nat,And32 0 12);(552,2%nat,Jump 2);
 (556,3%nat,CopyG 7 13);(559,3%nat,CopyG 6 14);(562,3%nat,CopyG 2 15)].
Lemma image:linked text gate /\ linked text finish.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition intersect s:=Z.land (regs s 12%nat) (regs s 0%nat).
Definition next m:=if m=?0 then 554 else 398.
Definition test_y bias:=segment (bias+pc) text 2.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem tested bias parent e caller p:placement e -> loaded Dalek bias (mem e) (writable e) ->
 ip p=bias+pc+389 -> accounted e (writable e) p -> well_formed(machine p) ->
 StrictMatchState.context bias parent e caller (machine p) -> 0<=regs(machine p) 0%nat<256 ->
 exists q,test_y bias p=Some q /\ ip q=bias+pc+next (regs(machine q) 12%nat) /\
 accounted e (writable e) q /\ well_formed(machine q) /\ StrictMatchState.context bias parent e caller (machine q) /\
 regs(machine q) 12%nat=intersect (machine p) /\ regs(machine q) 0%nat=regs(machine p) 0%nat.
Proof.
 intros P I At Paid W C Byte;set(o:=bias+pc);set(s:=machine p) in *;set(m:=intersect s).
 assert (B:0<=m<256) by (apply EligibleLanes.masked_byte,Byte).
 set(v:=with_zf (set s 12 m) (m=?0)).
 assert (Run:run 2 (ScalarBytes.fetch o text) (State(Running 389) s (carry p))=Some(State(Running(next m)) v (Some false),[])).
 { apply (InstructionRoute.checked _ _ _ (proj1 image));cbn [gate follow step loc cpu_state cf option_map eval_condition with_zf flag app].
   fold (intersect s);fold m;rewrite (Z.mod_small m (2^32)) by lia;unfold next;destruct(m=?0);reflexivity. }
 destruct(mapped_now _ _ _ I _ _ _ Paid (ScoreSetup.image Dalek)) as [Map Sep].
 destruct(at_segment _ _ p o text 2 _ _ _ Paid At Map Sep Run (Forall_nil _)) as [Step End].
 eexists;split;[exact Step|split;[reflexivity|split;[exact End|split;[exact (segment_wf _ _ _ _ _ W Step)|split;[|split;reflexivity]]]]].
 change (StrictMatchState.context bias parent e caller v);apply(StrictMatchState.preserve _ _ _ _ _ _ P C).
 - intros r K;change (put (regs s) 12 m r=regs s r);unfold put;destruct(Nat.eqb_spec 12 r);[subst;unfold StrictMatchState.kept in K;simpl in K;intuition discriminate|reflexivity].
 - intros x X;reflexivity.
 - apply (StrictMatchState.constants _ _ _ _ _ C).
Qed.

Definition args bias (zero:bool):=segment (bias+pc) text (if zero then 4 else 5).
Definition mask (zero:bool) s:=if zero then 0 else intersect s.
Lemma raw (zero:bool) o s c :0<=regs s 0%nat<256 ->
 exists u,run (if zero then 4 else 5) (ScalarBytes.fetch o text) (State(Running(if zero then 554 else 549)) s c)=
 Some(State(Running 565) u (Some false),[]) /\ regs u 0%nat=mask zero s /\ regs u 7%nat=regs s 13%nat /\
 regs u 6%nat=regs s 14%nat /\ regs u 2%nat=regs s 15%nat /\ regs u 5%nat=regs s 5%nat /\ mem u=mem s.
Proof.
 intro B;destruct zero.
 - destruct(StrictRCall.zero_raw o s c) as [u [R [_ Rest]]];exists u;exact (conj R Rest).
 - pose proof(EligibleLanes.masked_byte (regs s 12%nat) (regs s 0%nat) B) as Bound;fold (intersect s) in Bound.
   set(m:=intersect s);set(v:=set (set (set (with_zf (set s 0 m) (m=?0)) 7 (regs s 13%nat)) 6 (regs s 14%nat)) 2 (regs s 15%nat)).
   exists v;split;[|repeat split;reflexivity]. apply (InstructionRoute.checked _ _ _ (proj2 image)).
   cbn [finish follow step loc cpu_state cf option_map app];rewrite Z.land_comm;fold (intersect s);fold m;
   rewrite (Z.mod_small m (2^32)) by lia;reflexivity.
Qed.
Theorem arguments (zero:bool) bias parent e caller p:loaded Dalek bias (mem e) (writable e) ->
 ip p=bias+pc+(if zero then 554 else 549) -> accounted e (writable e) p -> well_formed(machine p) ->
 StrictMatchState.context bias parent e caller (machine p) -> 0<=regs(machine p) 0%nat<256 ->
 exists q,args bias zero p=Some q /\ ip q=bias+pc+565 /\ accounted e (writable e) q /\ well_formed(machine q) /\
 ScoreSaved.frame bias parent e caller (machine q) /\ StrictMatchState.flags e (machine q) /\ ScoreTail.arguments e (mask zero (machine p)) (machine q).
Proof.
 intros I At Paid W C Byte;set(o:=bias+pc);destruct(raw zero o (machine p) (carry p) Byte) as [u [Run [A [DI [SI [DX [FP M]]]]]]].
 destruct(mapped_now _ _ _ I _ _ _ Paid (ScoreSetup.image Dalek)) as [Map Sep].
 destruct(at_segment _ _ p o text _ _ _ _ Paid At Map Sep Run (Forall_nil _)) as [Step End].
 eexists;split;[exact Step|split;[reflexivity|split;[exact End|split;[exact(segment_wf _ _ _ _ _ W Step)|]]]].
 change (ScoreSaved.frame bias parent e caller u /\ StrictMatchState.flags e u /\ ScoreTail.arguments e (mask zero (machine p)) u).
 split;[eapply ScoreSaved.keep;[exact (StrictMatchState.saved _ _ _ _ _ C)|exact FP|intros x _;now rewrite M]|split].
 - intros j J;cbv zeta;rewrite M;exact (StrictMatchState.eligibility _ _ _ _ _ C j J).
 - unfold ScoreTail.arguments;rewrite DI,SI,DX;exact(conj A (StrictMatchState.args _ _ _ _ _ C)).
Qed.
End Iteration.
