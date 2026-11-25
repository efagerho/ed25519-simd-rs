From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.MemoryGeometry.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchDecode KeySquare.
From Ed25519Simd.VerifyBatch Require DecoderFinish DecoderFrame RootDecision KeyReturn ReturnedPoint RootAccept
 SignedRoot SignatureFinish FinishTrace.
Local Open Scope Z_scope.

Record trace:=Trace { key:KeyReturn.trace; sig_entry:cursor; signature:FinishTrace.trace }.
Definition returned t:=FinishTrace.returned(signature t).
Definition observe pol bias e p bank:=bind (KeyReturn.observe pol bias e p bank) (fun r=>
 bind (SignatureFinish.enter bias (KeyReturn.returned r)) (fun s=>option_map (Trace r s)
  (FinishTrace.execute bias s (SignedRoot.after_masks(KeyReturn.signed r))))).
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record post pol bias e t : Prop:=Post {
 key_result:KeyReturn.post pol bias e (key t);
 signature_entry:DecoderFinish.entry true pol bias e (sig_entry t);
 call_memory:preserved (fun x=>~span (link_slot pol e) 8 x) (mem(machine(KeyReturn.returned(key t)))) (mem(machine(sig_entry t)));
 signature_result:FinishTrace.post true pol bias e (sig_entry t) (signature t);
 at_masks:ip(returned t)=base bias+222;
 writes:accounted e (writable e) (returned t);
 key_mask:regs(machine(returned t)) 13%nat=regs(machine(KeyReturn.returned(key t))) 0%nat;
 key_accepts:forall j,(j<8)%nat -> (Z.testbit (regs(machine(returned t)) 13%nat) (Z.of_nat j)=true <-> RootDecision.decodable e j);
 signature_mask:0<=regs(machine(returned t)) 0%nat<256 /\ forall j,(j<8)%nat ->
  Z.testbit (regs(machine(returned t)) 0%nat) (Z.of_nat j)=RootAccept.bits true e (machine(FinishTrace.test(signature t))) j
}.

Theorem from_decoder pol bias e p bank : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> BatchDecode.entry pol bias e p -> well_formed(machine p) ->
 exists t,observe pol bias e p bank=Some t /\ post pol bias e t.
Proof.
 intros P I Al E W;destruct(KeyReturn.from_decoder _ _ _ _ bank P I Al E W) as [r [A R]].
 destruct(SignatureFinish.checked _ _ _ _ P I R) as [s [B [Entry [Mask Keep]]]].
 destruct(FinishTrace.checked true pol bias e s (SignedRoot.after_masks(KeyReturn.signed r)) P I Entry) as [rs [C Done]].
 pose proof(FinishTrace.coordinates _ _ _ _ _ _ Done) as Out.
 assert (K:regs(machine(FinishTrace.returned rs)) 13%nat=regs(machine(KeyReturn.returned r)) 0%nat)
   by (rewrite (FinishTrace.callee_registers _ _ _ _ _ _ Done) by discriminate;exact Mask).
 exists(Trace r s rs);split;[unfold observe;rewrite A;cbn [bind];rewrite B;cbn [bind];now rewrite C|].
 constructor;cbn [key sig_entry signature returned];try assumption.
 - exact (ReturnedPoint.resume _ _ _ _ _ _ Out).
 - exact (ReturnedPoint.writes _ _ _ _ _ _ Out).
 - intros j J;change (Z.testbit (regs(machine(FinishTrace.returned rs)) 13%nat) (Z.of_nat j)=true <-> RootDecision.decodable e j);rewrite K;exact (KeyReturn.accepts _ _ _ _ R j J).
 - split;[exact (FinishTrace.mask_byte _ _ _ _ _ _ Done)|intros j J;exact (proj1(FinishTrace.mask_bit _ _ _ _ _ _ Done j J))].
Qed.
End Iteration.
