From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions isa.IndexedLoad isa.VectorMoves execution.WordSemantics execution.WordBounds
 execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.ScalarWords execution.RipBroadcasts
 execution.InstructionRoute execution.MappedFetch memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.DalekPostHash Require FilterBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require StrictFilterCall.
Import ListNotations. Local Open Scope Z_scope.

Definition site:=FilterBytes.address.
Definition text:=FilterBytes.symbol_bytes.
Definition input:=LoadZ 20 (Addr 7 false 0).
Definition start:list line:=[(0,4%nat,Sub64 4 8);(4,6%nat,VectorMove(VectorMoves.Input input))].
Definition constants:=RipBroadcasts.route 4 10 28 (DecoderFrame.helper+0xde0-site).
Lemma linked_start:linked text start /\ linked text constants.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute bias:=segment (bias+site) text 6.

Record result bias e p q:Prop:=Result {
 pc:ip q=bias+site+50; writes:accounted e (writable e) q; words:well_formed(machine q);
 gpr:regs(machine q)=put (regs(machine p)) 4 (StrictFilterCall.slot e-8);
 memory_after:mem(machine q)=mem(machine p); history:log q=log p;
 addresses:forall j,(j<8)%nat -> vectors(machine q) j 20%nat=read_word (mem(machine p)) (PrepareOutputs.dest e+8*Z.of_nat j);
 field_constants:forall i j,(i<4)%nat -> vectors(machine q) j (28+i)%nat=DecoderFrame.constant i
}.

Theorem checked bias e prep p : placement e -> loaded Dalek bias (mem e) (writable e) ->
 StrictFilterCall.entry bias e prep p -> exists q,execute bias p=Some q /\ result bias e p q.
Proof.
 intros P I E;set (s:=machine p) in *;set (top:=StrictFilterCall.slot e);set (o:=bias+site).
 pose proof(StrictFilterCall.stack _ _ _ _ E) as SP;pose proof(StrictFilterCall.keys _ _ _ _ E) as DI;fold s top in SP,DI.
 destruct(stack_ok _ P) as [[L H] Al];assert (Fit:word64 top /\ word64(top-8) /\ 8<top /\ word64(PrepareOutputs.dest e))
   by (unfold top,StrictFilterCall.slot,PrepareOutputs.dest,common_top,Rows.frame,sp,word64 in *;lia).
 set (m:=IndexedLoads.execute [input] (with_zf (set s 4 (top-8)) false)).
 assert (First:run 2 (ScalarBytes.fetch o text) (State(Running 0) s (LinkedRun.carry p))=Some(State(Running 10) m (Some false),[])).
 { apply (InstructionRoute.checked _ _ _ (proj1 linked_start));cbn [start follow loc cpu_state cf step option_map].
   rewrite SP,(word_fits _ (proj1 Fit));change (word 8) with 8;rewrite (word_fits _ (proj1(proj2 Fit))),
    (proj2(Z.eqb_neq (top-8) 0) ltac:(lia)),(proj2(Z.ltb_ge top 8) ltac:(lia));reflexivity. }
 destruct(RipBroadcasts.load o text 4 10 28 _ m (Some false) (proj2 linked_start)) as [t [Last [G [M [_ [V Keep]]]]]].
 pose proof(run_append _ _ _ _ _ First _ _ _ Last) as Run.
 pose proof(StrictFilterCall.writes _ _ _ _ E) as Acc;destruct(mapped_now _ _ _ I _ _ _ Acc StrictFilterCall.in_filter) as [Map Sep].
 destruct(at_segment _ _ p o text 6 0 _ _ Acc ltac:(rewrite Z.add_0_r;exact (StrictFilterCall.pc _ _ _ _ E)) Map Sep Run (Forall_nil _))
   as [Next Paid];eexists;split;[exact Next|constructor].
 - reflexivity.
 - exact Paid.
 - exact (segment_wf _ _ _ _ _ (StrictFilterCall.words _ _ _ _ E) Next).
 - exact G.
 - exact M.
 - apply app_nil_r.
 - intros j J;change (vectors t j 20%nat=read_word (mem s) (PrepareOutputs.dest e+8*Z.of_nat j));rewrite Keep by lia.
   change (read_word (mem s) (word(regs s 7%nat+0)+8*Z.of_nat j)=read_word (mem s) (PrepareOutputs.dest e+8*Z.of_nat j)).
   rewrite DI,Z.add_0_r,(word_fits _ (proj2(proj2(proj2 Fit))));reflexivity.
 - intros i j K;change (vectors t j (28+i)%nat=DecoderFrame.constant i);rewrite V by exact K.
   destruct(mapped_now _ _ _ I _ _ _ Acc (BatchDecode.helper_in Dalek)) as [Helper _].
   pose proof(proj1(symbols _ _ _ _ I _ _ (BatchDecode.helper_in Dalek))) as Bound.
   change (read_word (mem s) (word(o+(DecoderFrame.helper+0xde0-site)+8*Z.of_nat i))=DecoderFrame.constant i).
   replace (o+(DecoderFrame.helper+0xde0-site)+8*Z.of_nat i) with
    (bias+DecoderFrame.origin+DecoderFrame.at_literal i-DecoderFrame.origin) by (unfold o,DecoderFrame.at_literal;ring).
   apply (DecoderFrame.mapped_value _ bias i K Helper).
   destruct Bound;pose proof(DecoderFrame.offsets _ K);unfold DecoderFrame.field_offset,DecoderFrame.at_literal,DecoderFrame.helper,word64 in *;lia.
Qed.
