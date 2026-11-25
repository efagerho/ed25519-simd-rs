From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.AlignedRows execution.RipBroadcasts
 execution.InstructionRoute execution.QwordBlock memory.WriteTrace memory.ByteMemory memory.MemoryGeometry.
From Curve25519 Require Import Radix51.
From Ed25519Simd.Dalek Require Encoding.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require StrictRStart RootMasks.
Import ListNotations. Local Open Scope Z_scope.
Local Notation pc:=(ScoreSetup.callee Dalek).
Local Notation text:=(ScoreSetup.code Dalek).

Definition y e s j:=DecodedRows.coord (DecodedRows.buffer true e s) j 1.
Definition literal:=DecoderFrame.helper+0xde8-pc.
Definition execute bias:=segment (bias+pc) text 9.
Lemma image:linked text (AlignedRows.route false 67 0 3 320 5) /\
 linked text (RipBroadcasts.route 1 102 29 literal) /\ linked text (QwordBlock.route 112 RootMasks.conjunction).
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Lemma source bias parent e h r child score p : placement e ->
 ScoreStart.reached Dalek bias parent e h r child score -> StrictRStart.reached bias e score p ->
 regs(machine p) 3%nat=BatchDecode.point e true /\ DecodedRows.encoded_y true e (DecodedRows.buffer true e (machine p)).
Proof.
 intros P Start T;pose proof(CandidateEntry.unchanged _ _ _ _ _ _ _ _ P Start) as M.
 destruct Start as [Call [f [_ [Frame [_ Ready]]]]];split.
 - rewrite (StrictRStart.unchanged_regs _ _ _ _ T) by discriminate.
   rewrite (proj1(ScoreStart.arguments _ _ _ _ _ Ready)),(ScoreFrame.gpr _ _ _ _ _ Frame) by discriminate.
   exact (proj1(proj2(proj2(ScoreCall.args _ _ _ _ _ _ _ Call)))).
 - assert (G:PreparedInputs.signature e (machine p)).
   { eapply DecodedRows.keep;[|exact (PreparedInputs.signature_point _ _
     (ScoreBuffers.operands _ _ (ScoreCall.buffers _ _ _ _ _ _ _ Call)))].
     intros x X;rewrite (StrictRStart.memory _ _ _ _ T);apply M.
     pose proof(scratch_stack _ P);unfold CandidateEntry.retained,span,BatchDecode.point,BatchDecode.point_offset,
       FlatMemory.disjoint,Rows.frame,sp in *;lia. }
   exact (proj1(proj2 G)).
Qed.

Record loaded_y bias e p q:Prop:=Loaded {
 at_compare:ip q=bias+pc+130; writes:accounted e (writable e) q; words:well_formed(machine q);
 registers:regs(machine q)=regs(machine p); memory:mem(machine q)=mem(machine p); history:log q=log p;
 high:forall j,(j<8)%nat -> vectors(machine q) j 10%nat=RootMasks.high (y e (machine p) j);
 low:forall j,(j<8)%nat -> vectors(machine q) j 0%nat=y e (machine p) j 0%nat;
 mask:forall j,vectors(machine q) j 29%nat=radix-1;
 canonical:forall j,(j<8)%nat -> (Encoding.noncanonical (y e (machine p) j)=false <->
    BatchDecode.original_encoding true e j mod 2^255<Field.prime)
}.

Theorem checked bias parent e h r child score p : placement e -> loaded Dalek bias (mem e) (writable e) ->
 ScoreStart.reached Dalek bias parent e h r child score -> StrictRStart.reached bias e score p ->
 exists q,execute bias p=Some q /\ loaded_y bias e p q.
Proof.
 intros P I S T;destruct(source _ _ _ _ _ _ _ _ P S T) as [Ptr Raw].
 set (o:=bias+pc);set (s:=machine p) in *;set (a:=BatchDecode.point e true+320).
 destruct(scratch_ok _ P) as [[L U] Align].
 assert (Al:a mod 64=0) by (unfold a;replace 320 with (5*64) by ring;rewrite Z.mod_add by lia;apply BatchDecode.point_aligned,Align).
 destruct(AlignedRows.loads o text 5 67 0 3 320 a s (carry p) (proj1 image) ltac:(now rewrite Ptr)
    Al ltac:(unfold a,BatchDecode.point,BatchDecode.point_offset,fits64;cbn;lia)) as [v [Read [G [M [_ [Y _]]]]]].
 destruct(RipBroadcasts.load o text 1 102 29 literal v (carry p) (proj1(proj2 image))) as [b [Bcast [G' [M' [_ [Const Kept]]]]]].
 destruct(QwordBlock.execute o text RootMasks.conjunction 112 b (carry p) (proj2(proj2 image))) as [last [And [G'' [M'' [_ V]]]]].
 change (State(Running 102) v (carry p)) with (State(Running(AlignedRows.after false 67 0 3 320 5)) v (carry p)) in Bcast.
 pose proof(run_append _ _ _ _ _ Read _ _ _ (run_append _ _ _ _ _ Bcast _ _ _ And)) as Run.
 pose proof(StrictRStart.writes _ _ _ _ T) as Prev.
 destruct(mapped_now _ _ _ I _ _ _ Prev (ScoreSetup.image Dalek)) as [Map Apart].
 destruct(at_segment _ _ _ o text 9 67 _ _ Prev (StrictRStart.address _ _ _ _ T) Map Apart Run (Forall_nil _)) as [Next Paid].
 assert (Row:forall j i,(j<8)%nat -> (i<5)%nat -> vectors b j i=y e s j i).
 { intros j i J K;rewrite Kept by lia;etransitivity;[exact (Y j i K)|];unfold y;rewrite DecodedRows.memory_coord;reflexivity. }
 eexists;split;[exact Next|constructor];cbn [LinkedRun.finish machine cpu_state log].
 - reflexivity.
 - exact Paid.
 - exact (segment_wf _ _ _ _ _ (StrictRStart.words _ _ _ _ T) Next).
 - now rewrite G'',G',G.
 - now rewrite M'',M',M.
 - apply app_nil_r.
 - intros j J;rewrite V;change (RootMasks.high (vectors b j)=RootMasks.high (y e s j)).
   unfold RootMasks.high;repeat rewrite Row by (exact J || lia);reflexivity.
 - intros j J;rewrite V;exact (Row j 0%nat J ltac:(lia)).
 - intro j;rewrite V;change (vectors b j 29%nat=radix-1);etransitivity;[exact (Const j 0%nat ltac:(lia))|];rewrite M.
   replace (o+literal+8*Z.of_nat 0) with (bias+DecoderFrame.helper+0xde8) by (unfold o,literal;ring).
   destruct(mapped_now _ _ _ I _ _ _ Prev (BatchDecode.helper_in Dalek)) as [Helper _].
   eapply NativeScale.read_literal;[exact Helper|apply (proj1(symbols _ _ _ _ I _ _ (BatchDecode.helper_in Dalek)))|
     lia|vm_compute;discriminate|vm_compute;reflexivity].
 - intros j J;destruct(Raw j J) as [Bound Number];rewrite Encoding.digits_canonical by exact Bound.
   change (limbs (y e s j)<Field.prime <-> BatchDecode.original_encoding true e j mod 2^255<Field.prime);fold (y e s j) in Number;now rewrite Number.
Qed.
