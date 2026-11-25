From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds execution.MappedFetch abi.SysV
 memory.FlatMemory memory.ByteMemory memory.WriteTrace memory.MemoryGeometry.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require ScoreInputs ScoreSetup.
Import ListNotations. From Ed25519Simd.VerifyBatch Require ChunkContext.
Local Open Scope Z_scope.

Definition execute bias pc text q r s c:=ScoreSetup.execute (bias+pc) text (HashResume.resume bias q r s c).
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record entered pol bias pc e q r child:Prop:=Entered {
 target:ip child=bias+ScoreSetup.callee pol; writes:accounted e (writable e) child; words:well_formed(machine child);
 args:ScoreSetup.arguments (machine child) (Rows.frame e) (scratch e)
   (Sha512Challenge.Execution.after r (Rows.frame e+840)) (output e) (regs e 6%nat);
 stack_args:let m:=mem(machine child) in let t:=Rows.frame e in
   read_word m (t-8)=bias+pc+539 /\ read_word m (t+832)=regs e 9%nat /\ read_word m (t+840)=scratch e+512 /\ read_word m (t+848)=t;
 lanes:forall j,(j<8)%nat -> let b:=mem(machine child)(Rows.frame e+856+Z.of_nat j) in
   (b=0 \/ b=1) /\ (b=1 <-> HashLayout.eligible pol e j);
 buffers:ScoreBuffers.data e (machine child);
 validity:forall j,(j<8)%nat -> (Z.testbit (regs(machine child) 2%nat) (Z.of_nat j)=true <-> RootDecision.decodes true e j);
 digest:forall j,(j<8)%nat -> HashLayout.eligible pol e j ->
   Scalar.ScalarSpec.lane_input (buffer_words (mem(machine child)) (Rows.frame e)) j=
   little_endian (SHA512.Spec.sha512 (r_bytes(HashLayout.row e j)++key_bytes(HashLayout.row e j)++message(HashLayout.row e j)));
 wrapper:BatchWindow.metadata e (mem(machine child)) /\ BatchWindow.saved_caller e (machine child) /\
   regs(machine child) 12%nat=BatchWindow.next_count e;
 restart:ChunkContext.bindings e (machine child);
 frame:preserved (fun x=>~ScoreSetup.slots (Rows.frame e) x) (Sha512Challenge.Execution.after r) (mem(machine child));
 store_log:log child=NativeHash.history bias q++ScoreSetup.events (bias+pc) (Rows.frame e) (scratch e) (Sha512Challenge.Execution.after r)
}.

Theorem checked pol bias pc text e q r s c : ScoreSetup.bound pol pc text -> placement e -> loaded pol bias (mem e) (writable e) ->
 fits64 (bias+pc) (Z.of_nat(length text)) -> mapped (mem e) (bias+pc) text ->
 (forall x,bias+pc<=x<bias+pc+Z.of_nat(length text) -> ~writable e x) ->
 ScoreInputs.inputs pol e (machine q) -> NativeHash.returned pol bias (bias+pc) e q r -> HashResume.compatible r s -> well_formed s ->
 exists child,execute bias pc text q r s c=Some child /\ entered pol bias pc e q r child.
Proof.
 intros Code P I Fit Map Sep Before R C W;set (p:=HashResume.resume bias q r s c).
 pose proof(ScoreInputs.after_hash _ _ _ _ _ _ _ P Before R C) as Data.
 destruct(ScoreInputs.gprs _ _ _ Data) as [DS [N Out]].
 destruct(ScoreSetup.checked pol bias pc text e p Code P I Map Sep (NativeHash.back _ _ _ _ _ _ R)
   (eq_trans (proj1(proj2 C)) (NativeHash.stack _ _ _ _ _ _ R)) DS (HashResume.accounted _ _ _ _ _ _ _ c R C) W)
   as [child [Run Entry]];set (t:=Rows.frame e) in *;set (m:=mem s).
 pose proof(ScoreSetup.words _ _ _ _ _ _ Entry) as LastW.
 assert (Mem:mem(machine child)=replay m (ScoreSetup.events (bias+pc) t (scratch e) m)) by exact (ScoreSetup.memory _ _ _ _ _ _ Entry).
 assert (Kept:preserved (fun x=>~ScoreSetup.slots t x) m (mem(machine child))).
 { intros x X;rewrite Mem;apply (WriteTrace.frame _ _ (ScoreSetup.footprint _ _ _ _)),X. }
 destruct(stack_ok _ P) as [[L H] _];destruct(scratch_ok _ P) as [[D DH] _].
 destruct(ScoreSetup.readback (bias+pc) t (scratch e) m ltac:(destruct Fit;destruct Code as [_ Len];unfold word64;lia)
      ltac:(unfold t,Rows.frame,sp,word64 in *;lia) ltac:(unfold word64;lia) (proj2(proj2 W))) as [Back [Base [Digits [Digest Flags]]]].
 rewrite <-Mem in Back,Base,Digits,Digest,Flags.
 pose proof(ScoreSetup.stack_args _ _ _ _ _ _ Entry) as Args;change (ScoreSetup.arguments (machine child) t (scratch e) (m(t+840)) (regs s 14%nat) (regs s 13%nat)) in Args.
 rewrite Out,N in Args. exists child;split;[exact Run|constructor].
 - exact (ScoreSetup.target _ _ _ _ _ _ Entry).
 - exact (ScoreSetup.writes _ _ _ _ _ _ Entry).
 - exact LastW.
 - unfold m in Args;rewrite (proj1 C) in Args;exact Args.
 - exact (conj Back (conj (eq_trans Base (proj2(ScoreInputs.tables _ _ _ Data))) (conj Digits Digest))).
 - intros j J;cbv zeta;fold t;rewrite <-(read_word_byte _ (t+856) (Z.of_nat j) (proj2(proj2 LastW)) ltac:(lia)),Flags.
   rewrite read_word_byte by (apply W || lia);exact (ScoreInputs.flags _ _ _ Data j J).
 - eapply ScoreBuffers.keep;[|exact (ScoreInputs.buffers _ _ _ Data)];intros x X;apply Kept.
   destruct(scratch_stack _ P);unfold ScoreBuffers.region,ScoreSetup.slots,span,disjoint,t,Rows.frame,sp in *;lia.
 - intros j J;destruct Args as [_ [_ [_ [DX _]]]];rewrite DX;exact (ScoreInputs.r_valid _ _ _ Data j J).
 - intros j J On;etransitivity;[|exact (NativeHash.digest _ _ _ _ _ _ R j J On)];unfold Scalar.ScalarSpec.lane_input;f_equal.
   apply map_ext_in;intros k K;apply in_seq in K;unfold buffer_words;rewrite <-(proj1 C).
   apply preserved_read with (outside:=fun x=>~ScoreSetup.slots t x);[exact Kept|].
   intros i B;change (0<=i<8) in B;unfold ScoreSetup.slots,span;fold t;lia.
 - split.
   + eapply IndexStores.metadata_preserved;[|exact (ScoreInputs.metadata _ _ _ Data)].
     intros x X;apply Kept;unfold ScoreSetup.slots,span;unfold t in *;lia.
   + destruct(ScoreInputs.saved _ _ _ Data) as [Spills BP];split;[split|].
     * intros x X;rewrite Kept;[exact (Spills x X)|pose proof(BatchWindow.geometry _ _ X);unfold BatchWindow.external_byte,ScoreSetup.slots,span,t,Rows.frame,sp in *;lia].
     * rewrite (ScoreSetup.saved _ _ _ _ _ _ Entry) by (simpl;tauto);exact BP.
     * rewrite (ScoreSetup.saved _ _ _ _ _ _ Entry) by (simpl;tauto);exact (ScoreInputs.remaining _ _ _ Data).
 - apply (ChunkContext.preserve e s (machine child)).
   + constructor;[exact(ScoreInputs.gprs _ _ _ Data)|exact(ScoreInputs.next_descriptor _ _ _ Data)|exact(ScoreInputs.tables _ _ _ Data)].
   + exact(ScoreSetup.saved _ _ _ _ _ _ Entry).
   + intros x X;apply Kept;unfold ScoreSetup.slots,span,t in *;lia.
 - rewrite <-(proj1 C);exact Kept.
 - rewrite <-(proj1 C);exact (ScoreSetup.store_log _ _ _ _ _ _ Entry).
Qed.
End Iteration.
