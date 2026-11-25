From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds execution.ScalarWords execution.StoreHistory
 abi.SysV memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Machine Require abi.FramePointer.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require CandidateFrame LadderProduct.
Local Open Scope Z_scope.
Definition execute:=CandidateUnwind.execute.
Record result e candidate q:Prop:=Result {
 back:ip q=read_word (mem(machine candidate)) (CandidateDigest.top e);
 stack:regs(machine q) 4%nat=ScoreFrame.buffer e;
 saved:forall g,In g sysv_saved -> regs(machine q) g=regs(machine candidate) g;
 parent:preserved (CandidateFrame.outside e) (mem(machine candidate)) (mem(machine q));
 words:well_formed(machine q); log_ok:accounted e (writable e) q
}.

Theorem checked pol bias e candidate digest mid ladder stop:placement e -> loaded pol bias (mem e) (writable e) ->
 CandidateEntry.entry pol bias e candidate -> CandidateDigest.entry pol bias e candidate digest ->
 ReducedDigest.returned pol bias e digest mid -> LadderEntry.entry pol bias e mid ladder ->
 LadderProduct.meaning pol bias e ladder stop -> accounted e (writable e) stop ->
 exists q,execute pol bias stop=Some q /\ result e candidate q /\ mem(machine q)=mem(machine stop).
Proof.
 intros P I Entry D R L Q Paid;set (t:=CandidateDigest.top e).
 set(ret:=read_word (mem(machine candidate)) t);pose proof(CandidateEntry.words _ _ _ _ Entry) as CW.
 destruct(stack_ok _ P) as [[Lo Hi] _];pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)) as Pad.
 assert (Fit:536<t /\ t+8<2^64) by (unfold t,CandidateDigest.top,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia).
 pose proof(CandidateFrame.arguments _ _ _ _ _ _ _ _ Entry D R L Q) as Slots.
 destruct(CandidateUnwind.transfer pol bias (machine stop) t (regs(machine candidate)) ret (carry stop)
   (proj1 Fit) (proj2 Fit) (LadderProduct.stack _ _ _ _ _ Q) (read_word_bound _ _ (proj2(proj2 CW))) Slots)
   as [Raw [SP [R12 [BX Other]]]].
 destruct(mapped_now _ _ _ I _ _ _ Paid (ScoreStart.candidate_image pol)) as [Map _].
 destruct(StoreHistory.segment_checked (fun _=>False) _ _ _ _ _ _ _ (LadderProduct.next _ _ _ _ _ Q)
   Map ltac:(tauto) Raw (Forall_nil _)) as [Run Hist].
 eexists;split;[exact Run|split;[constructor|reflexivity]].
 - reflexivity.
 - change (regs(CandidateUnwind.restored (machine stop) t) 4%nat=ScoreFrame.buffer e);rewrite SP;unfold t,CandidateDigest.top;ring.
 - intros g K;destruct(Nat.eq_dec g 3) as [->|N3];[exact BX|];destruct(Nat.eq_dec g 12) as [->|N12];[exact R12|].
   rewrite <- (CandidateFrame.untouched _ _ _ _ _ _ _ _ D R L Q g K N3 N12).
   apply Other;try assumption;intro E;subst g;cbv [sysv_saved In] in K;intuition discriminate.
 - exact (CandidateFrame.outside_kept _ _ _ _ _ _ _ _ D R L Q).
 - exact (segment_wf _ _ _ _ _ (LadderProduct.words _ _ _ _ _ Q) Run).
 - eapply StoreHistory.account;[exact Paid|exact (StoreHistory.lend (fun _=>False) _ _ _ (fun x H=>False_rect _ H) Hist)].
Qed.
