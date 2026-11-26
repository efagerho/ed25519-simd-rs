From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MaskTransfer.
From Curve25519 Require Import Radix51.
From Curve25519 Require Radix51Digits.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchDecode KeySquare.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderPower PairedSetup SetupTail PowerWrites DecoderFinish FinishProduct RootTest RootAccept RootDecision.
Local Open Scope Z_scope.

Record trace:=Trace { test:RootTest.trace; selection:cursor; masks:MaskTransfer.bank }.
Definition incoming r:=SetupTail.masks (PairedSetup.signature_r (DecoderPower.setup_points (PowerWrites.before_power (RootTest.power r)))).
Definition observe pol bias e p bank:=bind (RootTest.observe pol bias e p bank) (fun r=>
 option_map (fun '(q,m)=>Trace r q m) (RootAccept.execute bias (RootTest.at_test r) (incoming r))).
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record post pol bias e t : Prop:=Post {
 test_result:RootTest.post pol bias e (test t);
 at_selection:ip (selection t)=base bias+1076;
 machine_words:well_formed(machine(selection t));
 writes:accounted e (writable e) (selection t);
 test_memory:mem(machine(selection t))=mem(machine(RootTest.at_test(test t)));
 scalar_registers:forall r,r<>10%nat -> regs(machine(selection t)) r=regs(machine(RootTest.at_test(test t))) r;
 numerator:forall j i,(i<5)%nat -> vectors(machine(selection t)) j i=NativeScale.row (machine(RootTest.at_test(test t))) (point e false) j i;
 curve_constants:forall i j,(i<4)%nat -> vectors(machine(selection t)) j (28+i)%nat=DecoderFrame.constant i;
 mask_byte:0<=regs(machine(selection t)) 10%nat<256;
 accepts_key:forall j,(j<8)%nat ->
   (Z.testbit (regs(machine(selection t)) 10%nat) (Z.of_nat j)=true <-> RootDecision.decodable e j) /\
   masks t 4%nat j=Radix51Digits.high_test (vectors(machine(RootTest.at_test(test t))) j) (-1)
}.

Theorem from_decoder pol bias e p bank : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> BatchDecode.entry pol bias e p -> well_formed(machine p) ->
 exists t,observe pol bias e p bank=Some t /\ post pol bias e t.
Proof.
 intros P I Al Entry W;destruct(RootTest.from_decoder _ _ _ _ bank P I Al Entry W) as [r [Run Proof]].
 destruct(RootTest.root_product _ _ _ _ Proof) as [PC [Paid [WF [G [_ [C Value]]]]]].
 destruct(RootTest.finish_arguments _ _ _ _ Proof) as [_ [_ [_ [_ [DI _]]]]].
 destruct(RootAccept.checked false pol bias e (RootTest.at_test r) (incoming r) P I PC Paid
   (eq_trans (G 7%nat ltac:(discriminate)) DI) (fun j=>C 1%nat j ltac:(lia)))
  as [q [out [M [End [Acc [Log [Flat [Regs [U [High [Byte Bits]]]]]]]]]]].
 exists(Trace r q out);split;[unfold observe;rewrite Run;cbn [bind];now rewrite M|].
 constructor;cbn [test selection masks];try assumption.
 - exact (RootAccept.words _ _ _ _ _ WF M).
 - intros i j N;rewrite High by lia;apply C,N.
 - intros j J;destruct(Bits j J) as [Bit Minus];rewrite Bit;split;[apply (RootDecision.bits _ _ _ _ Proof j J)|exact Minus].
Qed.
End Iteration.
