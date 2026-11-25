From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 memory.ByteMemory memory.WriteTrace abi.SysV.
From Machine Require abi.FramePointer abi.FrameRestore abi.FrameSlots.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require ScoreStart.
Import ListNotations. Local Open Scope Z_scope.

Definition area e x:=ScoreFrame.top e-48<=x.
Record frame bias parent e caller (s:cpu):Prop:=Frame {
 fp:regs s 5%nat=ScoreFrame.top e-8;
 slots:FrameRestore.saved (mem s) (ScoreFrame.top e) (regs(machine caller));
 link:read_word (mem s) (ScoreFrame.top e)=bias+parent+539;
 metadata:StageEntry.metadata e (mem s); spills:CallerSpills.saved e (mem s);
 outer_bp:regs(machine caller) 5%nat=regs e 5%nat;
 counter:regs(machine caller) 12%nat=Prologue.rows_left (regs e 6%nat)
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
 constructor;[exact BP| | | | |exact RBP|exact Count].
 - intros g G;rewrite (read_slot _ _ _ M _ G);apply FrameSlots.saved_words;[exact (proj1(ScoreCall.words _ _ _ _ _ _ _ C))|exact G].
 - rewrite (above_top _ _ _ Above);exact (proj1(ScoreCall.stack_args _ _ _ _ _ _ _ C)).
 - eapply IndexStores.metadata_preserved;[|exact Meta];intros x X;apply Above;unfold ScoreFrame.top;lia.
 - intros x X;rewrite Above;[apply Spills,X|unfold ScoreFrame.top,Rows.frame,sp in *;lia].
Qed.
Lemma keep bias parent e caller s u : frame bias parent e caller s ->
 regs u 5%nat=regs s 5%nat -> preserved (area e) (mem s) (mem u) -> frame bias parent e caller u.
Proof.
 intros F BP M;constructor.
 - rewrite BP;apply (fp _ _ _ _ _ F).
 - intros g G;rewrite (read_slot _ _ _ M _ G);apply (slots _ _ _ _ _ F),G.
 - rewrite (above_top e (mem s) (mem u) ltac:(intros x X;apply M;unfold area;lia));exact (link _ _ _ _ _ F).
 - eapply IndexStores.metadata_preserved;[|exact (metadata _ _ _ _ _ F)];intros x X;apply M;unfold area,ScoreFrame.top;lia.
 - intros x X;rewrite M;[exact (spills _ _ _ _ _ F x X)|unfold area,ScoreFrame.top,Rows.frame,sp in *;lia].
 - exact (outer_bp _ _ _ _ _ F).
 - exact (counter _ _ _ _ _ F).
Qed.
