From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarWords memory.ByteMemory memory.FlatMemory memory.MemoryGeometry.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare DecoderSave SetupTail PairedSetup
 DecoderPower PowerWrites DecoderResume.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderSpills SetupValues NativeWords RootTest DecoderFinish FinishProduct PairReturn KeyReturn SignedRoot RootCandidate Selection FinishTrace ExtendedPoint RootAccept RootAdjusted RootSign ReturnedPoint SignatureFinish.
Local Open Scope Z_scope.

Lemma above pol e x : DecoderSpills.area pol e x -> link_slot pol e+648<=x /\ sp e-2048<=x<sp e.
Proof.
 unfold DecoderSpills.area,DecoderSpills.top,link_slot,DecoderFrame.top.
 pose proof(Z.mod_pos_bound (common_top pol e-112-40) 64 ltac:(lia)).
 unfold common_top,Rows.frame,sp in *;destruct pol;lia.
Qed.
Lemma away_stack pol e x : DecoderSpills.protected pol e x ->
 x<link_slot pol e-1936 \/ link_slot pol e+648<=x.
Proof.
 intros [A|[S _]];[right;exact(proj1(above _ _ _ A))|].
 unfold DecoderSpills.top,link_slot,DecoderFrame.top in *.
 pose proof(Z.mod_pos_bound (common_top pol e-112-40) 64 ltac:(lia)).
 unfold common_top,Rows.frame,sp in *;destruct pol;lia.
Qed.
Lemma off_point sig pol e x : placement e -> DecoderSpills.protected pol e x -> ~span (point e sig) 1280 x.
Proof. intros P [X|[_ F]];[|apply F];destruct(above _ _ _ X);destruct(scratch_stack _ P);
 unfold span,disjoint,point,point_offset in *;destruct sig;lia. Qed.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Lemma at_power pol bias e p bank t : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> BatchDecode.entry pol bias e p -> well_formed(machine p) ->
 DecoderPower.observe bias p bank=Some t -> DecoderSpills.retained pol e (machine p) (mem(machine(exponent_entry t))).
Proof.
 intros P I Al E W;destruct(BatchDecode.from_decoder _ _ _ _ P I E) as [a [A SA]].
 pose proof(DecoderSpills.at_setup _ _ _ _ _ P I E A) as Saved.
 destruct(SetupTail.from_setup false _ _ _ a bank P I Al SA) as [k [B [SqK CK]]].
 pose proof(segment_wf _ _ _ p _ W A) as WA.
 destruct(SetupValues.setup_fields false _ _ _ P I _ _ _ Al SA WA B) as [_ AK].
 destruct(switch _ _ _ _ P I CK) as [b [C [SB More]]].
 pose proof(segment_wf _ _ _ _ _ (NativeWords.input_words_after _ _ _ _ WA B) C) as WB.
 destruct(SetupTail.from_setup true _ _ _ b (SetupTail.masks k) P I Al SB) as [r [D [SqR CR]]].
 destruct(SetupValues.setup_fields true _ _ _ P I _ _ _ Al SB WB D) as [_ AR].
 destruct(DecoderPower.from_setup _ _ _ _ P I CR) as [v [F [_ Enter]]].
 unfold DecoderPower.observe,observe_pair,SetupTail.observe;rewrite A;cbn [bind];rewrite B;cbn [bind];
 rewrite C;cbn [bind];rewrite D;cbn [bind option_map signature_r];rewrite F;intro Eq;injection Eq as <-.
 intros x X;change (mem(machine v) x=spill (regs(machine p)) (mem(machine p)) (DecoderSpills.top pol e) DecoderSpills.registers x);pose proof(away_stack _ _ _ X) as Away.
 rewrite Enter by (unfold span;lia).
 rewrite AR;[|split;[fold (link_slot pol e);lia|apply (off_point true pol e x P X)]].
 rewrite More by (unfold span;lia).
 rewrite AK;[exact (Saved x X)|split;[fold (link_slot pol e);lia|apply (off_point false pol e x P X)]].
Qed.

Theorem at_finish pol bias e p bank t : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> BatchDecode.entry pol bias e p -> well_formed(machine p) ->
 RootTest.observe pol bias e p bank=Some t -> RootTest.post pol bias e t ->
 DecoderSpills.retained pol e (machine p) (mem(machine(RootTest.finish_entry t))).
Proof.
 intros P I Al E W Run T;unfold RootTest.observe,PowerWrites.observe in Run.
 destruct(DecoderPower.observe bias p bank) as [inputs|] eqn:A;[|discriminate];cbn [bind] in Run.
 destruct(PowerWrites.execute _ _ _ _) as [back|] eqn:B;[|discriminate];cbn [option_map bind after_power] in Run.
 destruct(DecoderFinish.enter _ _) as [begin|] eqn:C;[|discriminate];cbn [bind] in Run.
 destruct(FinishProduct.finish bias begin);[|discriminate];injection Run as <-.
 destruct(RootTest.power_result _ _ _ _ T) as [D [R _]].
 destruct(DecoderResume.after_return _ _ _ _ _ P (proj1(proj2 D)) (NativeWords.pow2_entry_words _ _ _ _ W A) R) as [Ready F].
 destruct(DecoderFinish.from_power _ _ _ _ P I Ready) as [q [C' [_ [G _]]]];change (DecoderFinish.enter bias (LocatedReturn.resumed back)=Some q) in C';rewrite C in C';injection C' as <-.
 pose proof(at_power _ _ _ _ _ _ P I Al E W A) as Saved.
 intros x X;change (mem(machine begin) x=spill (regs(machine p)) (mem(machine p)) (DecoderSpills.top pol e) DecoderSpills.registers x);pose proof(away_stack _ _ _ X) as Away.
 rewrite G by (unfold span;lia);rewrite F;[exact (Saved x X)|].
 change (~(link_slot pol e+8<=x<link_slot pol e+8+640 \/
   link_slot pol e-1928+1928-1936<=x<link_slot pol e-1928+1928-8));lia.
Qed.

Definition first_test t:=Selection.test(RootCandidate.decision(SignedRoot.candidate(KeyReturn.signed(PairReturn.key t)))).

Lemma observed_test pol bias e p bank t : PairReturn.observe pol bias e p bank=Some t ->
 RootTest.observe pol bias e p bank=Some(first_test t).
Proof.
 unfold PairReturn.observe,KeyReturn.observe,SignedRoot.observe,RootCandidate.observe,Selection.observe.
 destruct(RootTest.observe pol bias e p bank) as [r|];[|discriminate];cbn [bind].
 destruct(RootAccept.execute _ _ _) as [[v m]|];[|discriminate];cbn [option_map bind].
 destruct(RootCandidate.execute _ _) as [x|];[|discriminate];cbn [option_map bind].
 destruct(RootAdjusted.execute _ _ _) as [[q k]|];[|discriminate];cbn [option_map bind].
 destruct(RootSign.execute _ _ _) as [[s ks]|];[|discriminate];cbn [option_map bind].
 destruct(ReturnedPoint.execute _ _) as [z|];[|discriminate];cbn [option_map bind].
 destruct(SignatureFinish.enter _ _) as [d|];[|discriminate];cbn [bind].
 destruct(FinishTrace.execute _ _ _);[|discriminate];intro H;injection H as <-;reflexivity.
Qed.

Theorem after_both pol bias e p bank t : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> BatchDecode.entry pol bias e p -> well_formed(machine p) ->
 PairReturn.observe pol bias e p bank=Some t -> PairReturn.post pol bias e t ->
 DecoderSpills.retained pol e (machine p) (mem(machine(PairReturn.returned t))).
Proof.
 intros P I Al E W Run T;pose proof(PairReturn.key_result _ _ _ _ T) as Key.
 pose proof(Selection.test_result _ _ _ _ (RootCandidate.selection _ _ _ _ (SignedRoot.raw _ _ _ _
   (KeyReturn.signed_result _ _ _ _ Key)))) as Test.
 pose proof(at_finish _ _ _ _ _ _ P I Al E W (observed_test _ _ _ _ _ _ Run) Test) as Saved.
 intros x X;pose proof(away_stack _ _ _ X) as Away.
 assert (Protected:forall sig,ExtendedPoint.protected sig pol e x).
 { intro sig;pose proof(off_point sig pol e x P X);unfold ExtendedPoint.protected,span in *;lia. }
 unfold PairReturn.returned.
 rewrite (FinishTrace.frame _ _ _ _ _ _ (PairReturn.signature_result _ _ _ _ T) x (Protected true)),
   (PairReturn.call_memory _ _ _ _ T x ltac:(unfold span;lia)),
   (KeyReturn.frame _ _ _ _ Key x (Protected false)).
 exact (Saved x X).
Qed.
End Iteration.
