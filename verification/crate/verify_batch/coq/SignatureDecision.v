From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.MemoryGeometry memory.FlatMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Return BatchDecode KeySquare.
From Ed25519Simd.VerifyBatch Require PairReturn KeyReturn SignedRoot RootCandidate Selection RootTest RootDecision
 RootAccept FinishTrace FinishProduct SetupValues SetupTail PowerInputs PowerWrites ExtendedPoint.
Local Open Scope Z_scope.

(* The first finish can write X, Z, and T of A. The second finish reads R
   and the upper half of the paired exponentiation result. *)
Lemma disjoint_inputs pol e x : placement e -> RootTest.operand_bytes true pol e x ->
 ExtendedPoint.protected false pol e x /\ ~span (link_slot pol e) 8 x /\ ~(link_slot pol e-24<=x<link_slot pol e).
Proof.
 intros P X;destruct(scratch_stack _ P);pose proof(depth pol e);
 unfold RootTest.operand_bytes,ExtendedPoint.protected,BatchDecode.point,BatchDecode.point_offset,
 DecoderFinish.power_offset,span,disjoint in *;lia.
Qed.

Theorem bits pol bias e t : placement e -> PairReturn.post pol bias e t -> forall j,(j<8)%nat ->
 Z.testbit (regs(machine(PairReturn.returned t)) 0%nat) (Z.of_nat j)=true <-> RootDecision.decodes true e j.
Proof.
 intros P T j J;rewrite (proj2(PairReturn.signature_mask _ _ _ _ T) j J).
 pose proof(PairReturn.key_result _ _ _ _ T) as Key.
 pose proof(Selection.test_result _ _ _ _ (RootCandidate.selection _ _ _ _ (SignedRoot.raw _ _ _ _
   (KeyReturn.signed_result _ _ _ _ Key)))) as First.
 set (r:=Selection.test(RootCandidate.decision(SignedRoot.candidate(KeyReturn.signed(PairReturn.key t))))) in *.
 set (a:=RootTest.finish_entry r) in *;set (b:=PairReturn.sig_entry t).
 set (q:=FinishTrace.test(PairReturn.signature t)).
 assert (Stayed:preserved (RootTest.operand_bytes true pol e) (mem(machine a)) (mem(machine b))).
 { intros x X;destruct(disjoint_inputs _ _ _ P X) as [Other [Stack _]].
   unfold b;rewrite (PairReturn.call_memory _ _ _ _ T x Stack);exact (KeyReturn.frame _ _ _ _ Key x Other). }
 set (prepared:=PowerWrites.before_power(RootTest.power r)).
 pose proof(FinishTrace.test_result _ _ _ _ _ _ (PairReturn.signature_result _ _ _ _ T)) as Last;fold b q in Last.
 apply (RootDecision.from_comparison true pol bias e (SetupTail.after_square(PowerInputs.half prepared true)) q).
 - exact (proj1(proj2(proj1(proj1(RootTest.power_result _ _ _ _ First))))).
 - eapply RootTest.at_comparison;[apply (RootTest.operands_preserved _ _ _ _ _ (RootTest.initial_operands _ _ _ _ First true) Stayed)|exact Last].
 - intros lane i L I;destruct(RootTest.root_product _ _ _ _ First) as [_ [_ [_ [_ [KeepA _]]]]].
   destruct Last as [_ [_ [_ [_ [KeepR _]]]]];fold a in KeepA.
   etransitivity;[|exact (proj1(RootTest.setup_fields_live _ _ _ _ First true lane i L I))].
   apply SetupValues.keep_row with (protect:=RootTest.operand_bytes true pol e);[|intros x X;right;unfold span;lia|exact L|exact I].
   intros x X;destruct(disjoint_inputs _ _ _ P X) as [_ [_ Safe]].
   rewrite (KeepR x Safe),(Stayed x X);symmetry;apply KeepA,Safe.
 - exact J.
Qed.
