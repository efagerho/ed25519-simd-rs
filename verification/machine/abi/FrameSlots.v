From Coq Require Import List ZArith Lia.
From Machine Require Import abi.FramePointer abi.FrameRestore abi.SysV execution.LinkedCalls execution.WordBounds execution.WordSemantics
 memory.ByteMemory memory.FlatMemory memory.WriteTrace.
Local Open Scope Z_scope.

Lemma commit_word m pc a v:commit m (qword pc a v)=store_word m a v.
Proof. reflexivity. Qed.
Lemma saved_words pc top rs m : (forall r,word64(rs r)) ->
 FrameRestore.saved (replay m (FramePointer.stores pc top rs)) top rs.
Proof.
 intros W g [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
 cbn [FrameRestore.slot FramePointer.stores replay fold_left];repeat rewrite commit_word;
 repeat rewrite read_other_word by (unfold disjoint;lia);apply write_read_word,W.
Qed.
