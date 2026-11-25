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

Lemma fields_kept sig e sq a b : SetupValues.fields sig e sq a ->
 preserved (span (BatchDecode.point e sig) 1280) (mem(machine a)) (mem(machine b)) -> SetupValues.fields sig e sq b.
Proof.
 intros F M j i J I;pose proof(F j i J I) as Values;cbv zeta in Values|-*.
 assert (Rows:forall off,0<=off<=960 -> NativeScale.row (machine b) (BatchDecode.point e sig+off) j i=
    NativeScale.row (machine a) (BatchDecode.point e sig+off) j i).
 { intros off O;apply (SetupValues.keep_row _ _ _ _ M);[unfold span;lia|exact J|exact I]. }
 pose proof(Rows 0 ltac:(lia)) as First;rewrite Z.add_0_r in First;rewrite First,!Rows by lia;exact Values.
Qed.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem inputs pol bias e t : placement e -> PairReturn.post pol bias e t -> exists sq,
 KeySquare.squared true pol bias e sq /\ RootTest.operands true pol e (PairReturn.sig_entry t) /\
 SetupValues.fields true e sq (FinishTrace.test(PairReturn.signature t)).
Proof.
 intros P T.
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
 exists(SetupTail.after_square(PowerInputs.half prepared true));split.
 - exact (proj1(proj2(proj1(proj1(RootTest.power_result _ _ _ _ First))))).
 - split;[exact (RootTest.operands_preserved _ _ _ _ _ (RootTest.initial_operands _ _ _ _ First true) Stayed)|].
   eapply fields_kept;[exact (RootTest.setup_fields_live _ _ _ _ First true)|].
   intros x X;destruct(RootTest.root_product _ _ _ _ First) as [_ [_ [_ [_ [KeepA _]]]]].
   destruct Last as [_ [_ [_ [_ [KeepR _]]]]];fold a in KeepA.
   assert (O:RootTest.operand_bytes true pol e x) by (right;exact X).
   destruct(disjoint_inputs _ _ _ P O) as [_ [_ Safe]];rewrite (KeepR x Safe),(Stayed x O);symmetry;apply KeepA,Safe.
Qed.

Theorem bits pol bias e t : placement e -> PairReturn.post pol bias e t -> forall j,(j<8)%nat ->
 Z.testbit (regs(machine(PairReturn.returned t)) 0%nat) (Z.of_nat j)=true <-> RootDecision.decodes true e j.
Proof.
 intros P T j J;rewrite (proj2(PairReturn.signature_mask _ _ _ _ T) j J);destruct(inputs _ _ _ _ P T) as [sq [S [O F]]].
 eapply RootDecision.from_comparison;[exact S|eapply RootTest.at_comparison;[exact O|exact (FinishTrace.test_result _ _ _ _ _ _ (PairReturn.signature_result _ _ _ _ T))]|
   intros lane i L I;exact (proj1(F lane i L I))|exact J].
Qed.
End Iteration.
