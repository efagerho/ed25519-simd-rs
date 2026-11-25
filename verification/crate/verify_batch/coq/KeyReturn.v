From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.MemoryGeometry memory.FlatMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchDecode KeySquare.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderFinish RootTest Selection RootCandidate RootDecision
 SignedRoot ReturnedPoint ExtendedPoint.
Local Open Scope Z_scope.

Record trace:=Trace { signed:SignedRoot.trace; returned:cursor }.
Definition observe pol bias e p bank:=bind (SignedRoot.observe pol bias e p bank) (fun r=>
 option_map (Trace r) (ReturnedPoint.execute bias (SignedRoot.at_store r))).
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record post pol bias e t:Prop:=Post {
 signed_result:SignedRoot.post pol bias e (signed t);
 native_return:ReturnedPoint.result false pol bias e (SignedRoot.at_store(signed t)) (returned t);
 valid_byte:0<=regs(machine(returned t)) 0%nat<256;
 accepts:forall j,(j<8)%nat -> (Z.testbit (regs(machine(returned t)) 0%nat) (Z.of_nat j)=true <-> RootDecision.decodable e j);
 frame:preserved (ExtendedPoint.protected false pol e) (mem(machine(SignedRoot.begin(signed t)))) (mem(machine(returned t)))
}.

Theorem from_decoder pol bias e p bank : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> BatchDecode.entry pol bias e p -> well_formed(machine p) ->
 exists t,observe pol bias e p bank=Some t /\ post pol bias e t.
Proof.
 intros P I Al Entry W;destruct(SignedRoot.from_decoder _ _ _ _ bank P I Al Entry W) as [r [A S]].
 pose proof(RootCandidate.selection _ _ _ _ (SignedRoot.raw _ _ _ _ S)) as D;pose proof(Selection.test_result _ _ _ _ D) as T.
 pose proof(RootTest.finish_arguments _ _ _ _ T) as [_ [_ [_ [SP [DI [SI [Link _]]]]]]].
 set (st:=link_slot pol e) in *.
 assert (Back:read_word (mem(machine(SignedRoot.at_store r))) st=base bias+DecoderFinish.return_offset false).
 { rewrite <-Link;apply preserved_read with (outside:=SignedRoot.protected pol e);[exact (SignedRoot.before_x _ _ _ _ S)|].
   intros k B;change (0<=k<8) in B;pose proof(depth pol e);fold st in H;destruct(scratch_stack _ P);
   unfold SignedRoot.protected,point,point_offset,disjoint;fold st;unfold disjoint in *;lia. }
 destruct(ReturnedPoint.checked false pol bias e (SignedRoot.at_store r) P I (SignedRoot.start_store _ _ _ _ S)
  (SignedRoot.writes _ _ _ _ S) (SignedRoot.words _ _ _ _ S)
  ltac:(rewrite (SignedRoot.register _ _ _ _ S) by discriminate;exact SP)
  ltac:(rewrite (SignedRoot.register _ _ _ _ S) by discriminate;exact DI) (SignedRoot.high _ _ _ _ S) Back)
  as [q [B Out]].
 pose proof(Selection.mask_byte _ _ _ _ D) as Narrow.
 assert (Mask:regs(machine q) 0%nat=regs(machine(Selection.selection(RootCandidate.decision(SignedRoot.candidate r)))) 10%nat).
 { rewrite (ReturnedPoint.mask _ _ _ _ _ _ Out),(SignedRoot.byte _ _ _ _ S);apply Z.mod_small;lia. }
 exists(Trace r q);split;[unfold observe;rewrite A;cbn [bind];now rewrite B|constructor];cbn [returned signed].
 - exact S.
 - exact Out.
 - now rewrite Mask.
 - intros j J;rewrite Mask;exact (proj1(Selection.accepts_key _ _ _ _ D j J)).
 - intros x X;rewrite (ReturnedPoint.untouched _ _ _ _ _ _ Out x X);apply (SignedRoot.before_x _ _ _ _ S).
   unfold SignedRoot.protected,ExtendedPoint.protected in *;lia.
Qed.
End Iteration.
