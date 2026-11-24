From Coq Require Import List ZArith Lia.
From Machine Require Import execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.PrepareChunk Require CommonBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderFinish PairReturn KeyReturn FinishTrace ReturnedPoint
 DecoderEpilogue DecoderSpills SuspendedFrame RootDecision SignatureDecision.
Import ListNotations. Local Open Scope Z_scope.

Definition execute bias:=segment (base bias) text 10.
Record trace:=Trace { points:PairReturn.trace; returned:cursor }.
Definition observe pol bias e p bank:=bind (PairReturn.observe pol bias e p bank) (fun r=>
 option_map (Trace r) (execute bias (PairReturn.returned r))).
Record post pol bias e p t : Prop:=Post {
 decoded:PairReturn.post pol bias e (points t);
 resumes:ip(returned t)=bias+PrepareNative.common+142;
 writes:accounted e (writable e) (returned t);
 words:well_formed(machine(returned t));
 frame_top:regs(machine(returned t)) 4%nat=common_top pol e-104;
 restores:forall r,In r DecoderSpills.registers -> regs(machine(returned t)) r=regs(machine p) r;
 memory_after:mem(machine(returned t))=mem(machine(PairReturn.returned(points t)));
 mask_word:regs(machine(returned t)) 0%nat=
  256*regs(machine(PairReturn.returned(points t))) 0%nat+regs(machine(PairReturn.returned(points t))) 13%nat;
 key_bit:forall j,(j<8)%nat -> (Z.testbit (regs(machine(returned t)) 0%nat) (Z.of_nat j)=true <-> RootDecision.decodable e j);
 signature_bit:forall j,(j<8)%nat -> Z.testbit (regs(machine(returned t)) 0%nat) (8+Z.of_nat j)=true <->
  RootDecision.decodes true e j
}.

Theorem from_decoder pol bias e p bank : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> BatchDecode.entry pol bias e p -> well_formed(machine p) ->
 exists t,observe pol bias e p bank=Some t /\ post pol bias e p t.
Proof.
 intros P I Al E W;destruct(PairReturn.from_decoder _ _ _ _ bank P I Al E W) as [r [R T]].
 pose proof(SuspendedFrame.after_both _ _ _ _ _ _ P I Al E W R T) as Saved.
 set (d:=PairReturn.returned r) in *;set (s:=machine d) in *;set (o:=base bias).
 pose proof(PairReturn.signature_result _ _ _ _ T) as Sig.
 pose proof(FinishTrace.coordinates _ _ _ _ _ _ Sig) as Coords.
 pose proof(ReturnedPoint.words _ _ _ _ _ _ Coords) as WD.
 pose proof(PairReturn.signature_mask _ _ _ _ T) as [S _];fold d s in S.
 assert (A:0<=regs s 13%nat<256) by (unfold s,d;rewrite (PairReturn.key_mask _ _ _ _ T);apply (KeyReturn.valid_byte _ _ _ _ (PairReturn.key_result _ _ _ _ T))).
 destruct(DecoderEpilogue.masks o s (LinkedRun.carry d) S A) as [u [Pack [Mask [G M]]]].
 destruct(PairReturn.signature_entry _ _ _ _ T) as [_ [_ [_ [_ [_ [_ [_ [[_ [BP _]] _]]]]]]]].
 assert (U:regs u 5%nat=DecoderSpills.top pol e-8).
 { rewrite G by discriminate;unfold s,d,PairReturn.returned;rewrite (FinishTrace.callee_registers _ _ _ _ _ _ Sig) by discriminate;
   rewrite BP;unfold DecoderSpills.top;ring. }
 destruct(DecoderEpilogue.returns pol e o (machine p) u (Some false) P W U ltac:(rewrite M;exact Saved)) as
   [last [Ret [PC [SP [Memory [EAX Regs]]]]]].
 pose proof(run_append _ 2 _ _ _ Pack 8 _ _ Ret) as All.
 pose proof(PairReturn.writes _ _ _ _ T) as Acc;fold d in Acc.
 destruct(mapped_now _ _ _ I _ _ _ Acc (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ d o text 10 222 _ _ Acc (PairReturn.at_masks _ _ _ _ T) Map Sep All (Forall_nil _)) as [End Paid].
 set (q:=LinkedRun.finish o d (last,[])) in *.
 assert (State:machine q=cpu_state last) by reflexivity.
 assert (F:word64(bias+PrepareNative.common+142)).
 { destruct(proj1(symbols _ _ _ _ I _ _ (in_common pol))) as [L H].
   assert (142<Z.of_nat(length CommonBytes.symbol_bytes)) by (vm_compute;reflexivity);unfold word64;lia. }
 assert (Result:regs(machine q) 0%nat=DecoderEpilogue.packed (regs s 13%nat) (regs s 0%nat)) by (now rewrite State,EAX,Mask).
 exists(Trace r q);split;[unfold observe;rewrite R;cbn [bind];unfold execute;fold o d;now rewrite End|].
 constructor;cbn [points returned].
 - exact T.
 - change (absolute o last=bias+PrepareNative.common+142);unfold absolute;rewrite PC.
   destruct E as [_ [_ [_ [_ [_ [_ [Caller _]]]]]]];unfold DecoderSpills.top;now rewrite Caller,(word_fits _ F),(word_fits _ F).
 - exact Paid.
 - eapply segment_wf;[exact WD|exact End].
 - rewrite State,SP;unfold DecoderSpills.top;ring.
 - now rewrite State.
 - rewrite State,Memory;exact M.
 - rewrite Result;apply DecoderEpilogue.packed_value;assumption.
 - intros j J;rewrite Result,(proj1(DecoderEpilogue.bits _ _ (Z.of_nat j) A ltac:(lia)));exact (PairReturn.key_accepts _ _ _ _ T j J).
 - intros j J;rewrite Result,(proj2(DecoderEpilogue.bits _ _ (Z.of_nat j) A ltac:(lia)));exact (SignatureDecision.bits _ _ _ _ P T j J).
Qed.
