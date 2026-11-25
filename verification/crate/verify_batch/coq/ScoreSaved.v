From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 memory.ByteMemory memory.WriteTrace abi.SysV.
From Machine Require abi.FramePointer abi.FrameRestore abi.FrameSlots.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require ScoreStart.
Import ListNotations. Local Open Scope Z_scope.

Definition area e x:=x<Return.sp e-16384 \/ ScoreFrame.top e-48<=x.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record frame bias parent e caller (s:cpu):Prop:=Frame {
 fp:regs s 5%nat=ScoreFrame.top e-8;
 slots:FrameRestore.saved (mem s) (ScoreFrame.top e) (regs(machine caller));
 link:read_word (mem s) (ScoreFrame.top e)=bias+parent+539;
 metadata:BatchWindow.metadata e (mem s); spills:BatchWindow.saved e (mem s);
 outer_bp:regs(machine caller) 5%nat=regs e 5%nat;
 counter:regs(machine caller) 12%nat=BatchWindow.next_count e;
 globals:Prologue.context_registers e (machine caller);
 descriptor:BatchWindow.next_descriptor e (regs(machine caller) 3%nat);
 tables:CallerSpills.table_arguments e (mem s)
}.

Lemma read_slot e m n : preserved (area e) m n -> forall g,In g sysv_saved ->
 read_word n (ScoreFrame.top e-FrameRestore.slot g)=read_word m (ScoreFrame.top e-FrameRestore.slot g).
Proof.
 intros M g G;apply preserved_read with (outside:=area e);[exact M|intros k K;change (0<=k<8) in K;unfold area].
 destruct G as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];cbn [FrameRestore.slot];lia.
Qed.
Lemma above_top e m n : preserved (fun x=>ScoreFrame.top e<=x) m n ->
 read_word n (ScoreFrame.top e)=read_word m (ScoreFrame.top e).
Proof. intro M;apply preserved_read with (outside:=fun x=>ScoreFrame.top e<=x);[exact M|intros k K;change (0<=k<8) in K;lia]. Qed.

Theorem from_call pol bias parent e hash r caller s : ScoreCall.entered pol bias parent e hash r caller ->
 regs s 5%nat=ScoreFrame.top e-8 ->
 preserved (area e) (replay (mem(machine caller))
  (FramePointer.stores (bias+ScoreSetup.callee pol) (ScoreFrame.top e) (regs(machine caller)))) (mem s) ->
 frame bias parent e caller s.
Proof.
 intros C BP M;destruct(ScoreCall.wrapper _ _ _ _ _ _ _ C) as [Meta [[Spills RBP] Count]].
 assert (Above:preserved (fun x=>ScoreFrame.top e<=x) (mem(machine caller)) (mem s)).
 { intros x X;rewrite M by (unfold area;lia);apply (WriteTrace.frame _ _ (FramePointer.confined _ _ _));lia. }
 pose proof(ScoreCall.restart _ _ _ _ _ _ _ C) as [Globals Row T].
 constructor;[exact BP| | | | |exact RBP|exact Count|exact Globals|exact Row|].
 - intros g G;rewrite (read_slot _ _ _ M _ G);apply FrameSlots.saved_words;[exact (proj1(ScoreCall.words _ _ _ _ _ _ _ C))|exact G].
 - rewrite (above_top _ _ _ Above);exact (proj1(ScoreCall.stack_args _ _ _ _ _ _ _ C)).
 - eapply IndexStores.metadata_preserved;[|exact Meta];intros x X;apply Above;unfold ScoreFrame.top;lia.
 - intros x X;pose proof(BatchWindow.geometry _ _ X) as G.
   rewrite M;[rewrite (WriteTrace.frame _ _ (FramePointer.confined _ _ _));[apply Spills,X|]|];
     unfold area,BatchWindow.external_byte,ScoreFrame.top,Rows.frame,sp in *;lia.
 - eapply CallerSpills.keep_tables;[|exact T];intros x X;apply Above;unfold ScoreFrame.top;lia.
Qed.
Lemma keep bias parent e caller s u : frame bias parent e caller s ->
 regs u 5%nat=regs s 5%nat -> preserved (area e) (mem s) (mem u) -> frame bias parent e caller u.
Proof.
 intros F BP M;constructor.
 - rewrite BP;apply (fp _ _ _ _ _ F).
 - intros g G;rewrite (read_slot _ _ _ M _ G);apply (slots _ _ _ _ _ F),G.
 - rewrite (above_top e (mem s) (mem u) ltac:(intros x X;apply M;unfold area;lia));exact (link _ _ _ _ _ F).
 - eapply IndexStores.metadata_preserved;[|exact (metadata _ _ _ _ _ F)];intros x X;apply M;unfold area,ScoreFrame.top;lia.
 - intros x X;rewrite M;[exact (spills _ _ _ _ _ F x X)|pose proof(BatchWindow.geometry _ _ X);unfold BatchWindow.external_byte,area,ScoreFrame.top,Rows.frame,sp in *;lia].
 - exact (outer_bp _ _ _ _ _ F).
 - exact (counter _ _ _ _ _ F).
 - exact(globals _ _ _ _ _ F).
 - exact(descriptor _ _ _ _ _ F).
 - eapply CallerSpills.keep_tables;[|exact(tables _ _ _ _ _ F)];intros x X;apply M;unfold area,ScoreFrame.top;lia.
Qed.
End Iteration.
