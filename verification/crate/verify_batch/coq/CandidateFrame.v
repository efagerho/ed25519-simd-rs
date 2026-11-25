From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.StoreHistory abi.FrameSlots abi.SysV
 memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return.
From Ed25519Simd.VerifyBatch Require CandidateUnwind LadderProduct.
Local Open Scope Z_scope.
Local Notation top:=CandidateDigest.top.
Local Notation dst:=CandidateDigest.dst.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition outside e x:=~(dst e-5040<=x<ScoreFrame.buffer e+1280).
Section Frame.
Variables (pol:policy) (bias:Z) (e:cpu) (candidate digest mid ladder stop:cursor).
Hypothesis Entry:CandidateEntry.entry pol bias e candidate.
Hypothesis D:CandidateDigest.entry pol bias e candidate digest.
Hypothesis R:ReducedDigest.returned pol bias e digest mid.
Hypothesis L:LadderEntry.entry pol bias e mid ladder.
Hypothesis Q:LadderProduct.meaning pol bias e ladder stop.
Lemma since_digest x : ~(ReducedDigest.D.writable (dst e-8) (dst e) x) ->
 ~(dst e-8<=x<dst e) -> ~LadderProduct.region ladder x -> mem(machine stop) x=mem(machine digest) x.
Proof.
 intros Dig Push Prod;rewrite (StoreHistory.preserves _ _ _ (LadderProduct.history _ _ _ _ _ Q) x Prod),(LadderEntry.memory _ _ _ _ _ L).
 unfold commit;rewrite write_outside;[apply (ReducedDigest.outside _ _ _ _ _ R),Dig|].
 change (~(dst e-8<=x<dst e-8+8));lia.
Qed.
Lemma outside_kept : preserved (outside e) (mem(machine candidate)) (mem(machine stop)).
Proof.
 intros x X;destruct(LadderEntry.arguments _ _ _ _ _ L) as [SP [Pt _]].
 rewrite since_digest;unfold outside,ReducedDigest.D.writable,CandidateDigest.dst,CandidateDigest.top in X|-*;
 try solve [lia|unfold LadderProduct.region,LadderStage.private_stack;rewrite SP,Pt;unfold CandidateDigest.dst,CandidateDigest.top in *;lia].
 rewrite (CandidateDigest.memory _ _ _ _ _ D);unfold CandidateDigest.spills,CandidateDigest.call_store;
 cbn [app replay fold_left];unfold commit;repeat rewrite write_outside;try reflexivity;
 change (Z.of_nat 8) with 8;cbn [qword size address];unfold CandidateDigest.dst,CandidateDigest.top in *;lia.
Qed.
Lemma arguments:CandidateUnwind.slots (top e) (mem(machine stop)) (regs(machine candidate))
 (read_word (mem(machine candidate)) (top e)).
Proof.
 destruct(LadderEntry.arguments _ _ _ _ _ L) as [SP [Pt _]].
 assert (Header:preserved (fun x=>top e-16<=x<top e+8) (mem(machine digest)) (mem(machine stop))).
 { intros x X;apply since_digest;unfold ReducedDigest.D.writable,LadderProduct.region,LadderStage.private_stack;
   rewrite ?SP,?Pt;unfold CandidateDigest.dst,CandidateDigest.top in *;lia. }
 assert (Word:forall a,top e-16<=a -> a+8<=top e+8 ->
   read_word (mem(machine stop)) a=read_word (mem(machine digest)) a).
 { intros a Low High;apply (preserved_read 8 _ _ _ _ Header);intros k K;change (0<=k<8) in K;lia. }
 unfold CandidateUnwind.slots;repeat rewrite Word by lia;rewrite (CandidateDigest.memory _ _ _ _ _ D).
 unfold CandidateDigest.spills,CandidateDigest.call_store;cbn [app replay fold_left];rewrite !FrameSlots.commit_word;
 repeat split;repeat rewrite read_other_word by (unfold CandidateDigest.dst,disjoint;lia);
 try reflexivity;apply write_read_word,(CandidateEntry.words _ _ _ _ Entry).
Qed.
Lemma untouched g:In g sysv_saved -> g<>3%nat ->g<>12%nat -> regs(machine stop) g=regs(machine candidate) g.
Proof.
 intros G B T;rewrite (LadderProduct.saved _ _ _ _ _ Q),(LadderEntry.saved _ _ _ _ _ L),(ReducedDigest.saved _ _ _ _ _ R) by exact G;
 apply (CandidateDigest.saved _ _ _ _ _ D);assumption.
Qed.
End Frame.
End Iteration.
