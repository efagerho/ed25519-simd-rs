From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 memory.ByteMemory memory.WriteTrace abi.SysV.
From Machine Require abi.FramePointer abi.FrameRestore.
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

Lemma pushed o top rs m : replay m (FramePointer.stores o top rs)=
 Return.spill rs m top [5;3;12;13;14;15]%nat.
Proof.
 cbn [FramePointer.stores replay fold_left Return.spill];unfold commit,store_word;cbn [qword address size payload].
 replace (top-8-8) with (top-16) by ring;replace (top-16-8) with (top-24) by ring;
 replace (top-24-8) with (top-32) by ring;replace (top-32-8) with (top-40) by ring;
 replace (top-40-8) with (top-48) by ring;reflexivity.
Qed.
Lemma recovered o top rs m g : (forall r,word64(rs r)) -> In g sysv_saved ->
 read_word (replay m (FramePointer.stores o top rs)) (top-FrameRestore.slot g)=rs g.
Proof.
 intros W Member;rewrite pushed;destruct Member as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
 match goal with |- _=rs ?g =>
   let i:=eval compute in (match g with 5%nat=>0%nat|3%nat=>1%nat|12%nat=>2%nat|13%nat=>3%nat|14%nat=>4%nat|_=>5%nat end) in
   exact (spilled_word rs m top [5;3;12;13;14;15]%nat i g W eq_refl) end.
Qed.
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
 - intros g G;rewrite (read_slot _ _ _ M _ G);apply recovered;[exact (proj1(ScoreCall.words _ _ _ _ _ _ _ C))|exact G].
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
