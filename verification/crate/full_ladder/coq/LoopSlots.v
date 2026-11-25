From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordBounds execution.WordSemantics abi.SysV abi.FrameSlots
 memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.FullLadder Require Import LinkedBytes LoopFrame.
Local Open Scope Z_scope.

Lemma word_in_header slide s v a: intact slide s v -> top s-64<=a -> a+8<=top s+8 ->
 read_word (mem v) a=read_word (saved_memory slide s) a.
Proof. intros F L H;apply (preserved_read 8 _ _ _ _ (header_bytes _ _ _ F));intros k K;change (0<=k<8) in K;unfold header;lia. Qed.

Lemma arguments slide s v : intact slide s v -> well_formed s ->
 read_word (mem v) (top s-56)=regs s 8%nat /\ read_le 4 (mem v) (top s-64)=regs s 9%nat mod 2^32.
Proof.
 intros F W;split.
 - rewrite (word_in_header _ _ _ _ F) by lia;unfold saved_memory;rewrite replay_app.
   cbn [StageEntry.spill replay fold_left];rewrite !commit_word,read_other_word by (unfold disjoint;lia);apply write_read_word,W.
 - rewrite (preserved_read 4 _ _ _ _ (header_bytes _ _ _ F)) by (intros k K;change (0<=k<4) in K;unfold header;lia).
   unfold saved_memory;rewrite replay_app;cbn [StageEntry.spill replay fold_left];rewrite !commit_word.
   apply read_le_encoded;intros k K;unfold store_word;apply write_at;change (0<=k<4) in K;lia.
Qed.

Lemma saved slide s v : intact slide s v -> well_formed s -> FrameRestore.saved (mem v) (top s) (regs s).
Proof.
 intros F W g G;assert (Slot:8<=FrameRestore.slot g<=48)
  by (destruct G as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];cbn [FrameRestore.slot];lia).
 rewrite (word_in_header _ _ _ _ F) by lia;unfold saved_memory;rewrite replay_app.
 cbn [StageEntry.spill replay fold_left];rewrite !commit_word,!read_other_word by (unfold disjoint;lia).
 apply FrameSlots.saved_words;[apply W|exact G].
Qed.
Lemma link slide s v: intact slide s v -> read_word (mem v) (top s)=read_word (mem s) (top s).
Proof.
 intro F;rewrite (word_in_header _ _ _ _ F) by lia;unfold saved_memory;rewrite replay_app.
 cbn [StageEntry.spill replay fold_left];rewrite !commit_word,!read_other_word by (unfold disjoint;lia).
 apply (preserved_read 8 (fun x=>top s<=x));[intros x X;apply (WriteTrace.frame _ _ (FramePointer.confined _ _ _));lia|intros k K;change (0<=k<8) in K;lia].
Qed.
