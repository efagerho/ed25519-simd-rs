From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory.
From Machine Require execution.MaskTransfer.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchDecode KeySquare NativeScale.
From Ed25519Simd.VerifyBatch Require DecoderFrame RootTest Selection RootCandidate RootAdjusted RootSign RowProduct.
Local Open Scope Z_scope.

Record trace:=Trace { candidate:RootCandidate.trace; selected:cursor; at_store:cursor; after_masks:MaskTransfer.bank }.
Definition observe pol bias e p bank:=bind (RootCandidate.observe pol bias e p bank) (fun r=>
 bind (RootAdjusted.execute bias (RootCandidate.saved_x r) (Selection.masks(RootCandidate.decision r))) (fun '(x,k)=>
 option_map (fun '(s,m)=>Trace r x s m) (RootSign.execute bias x k))).
Record post pol bias e t : Prop:=Post {
 raw:RootCandidate.post pol bias e (candidate t);
 selection:exists k,RootAdjusted.result pol bias e (RootCandidate.saved_x(candidate t))
   (Selection.masks(RootCandidate.decision(candidate t))) (selected t) k;
 start_store:ip(at_store t)=base bias+1299;
 writes:accounted e (writable e) (at_store t);
 words:well_formed(machine(at_store t));
 regs_after:regs(machine(at_store t))=regs(machine(selected t));
 memory_after:mem(machine(at_store t))=mem(machine(selected t));
 high:RowProduct.constants(machine(at_store t));
 sign:forall j i,(j<8)%nat -> (i<5)%nat -> vectors(machine(at_store t)) j i=RootSign.adjusted (machine(selected t)) j i
}.

Theorem from_decoder pol bias e p bank : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> BatchDecode.entry pol bias e p -> well_formed(machine p) ->
 exists t,observe pol bias e p bank=Some t /\ post pol bias e t.
Proof.
 intros P I Al Entry W;destruct(RootCandidate.from_decoder _ _ _ _ bank P I Al Entry W) as [r [A R]].
 pose proof(RootCandidate.native _ _ _ _ R) as Data.
 pose proof(Selection.test_result _ _ _ _ (RootCandidate.selection _ _ _ _ R)) as T.
 destruct(RootTest.finish_arguments _ _ _ _ T) as [_ [_ [_ [SP [DI _]]]]].
 set (p0:=RootCandidate.saved_x r) in *;set (k0:=Selection.masks(RootCandidate.decision r)).
 destruct(RootAdjusted.checked false pol bias e p0 k0 P I (RootCandidate.next_call _ _ _ _ _ _ Data)
  (RootCandidate.writes _ _ _ _ _ _ Data) (RootCandidate.words _ _ _ _ _ _ Data)
  ltac:(rewrite (RootCandidate.saved_register _ _ _ _ R) by discriminate;exact SP)
  ltac:(rewrite (RootCandidate.saved_register _ _ _ _ R) by discriminate;exact DI)
  (RootCandidate.high _ _ _ _ _ _ Data)
  ltac:(intros j i J N;destruct(RootCandidate.live_x _ _ _ _ _ _ Data j i J N) as [V M];rewrite M;exact (eq_sym V)))
  as [q [k [B Selected]]].
 destruct(RootSign.checked pol bias e q k I (RootAdjusted.next _ _ _ _ _ _ _ Selected)
  (RootAdjusted.writes _ _ _ _ _ _ _ Selected) (RootAdjusted.words _ _ _ _ _ _ _ Selected) (RootAdjusted.high _ _ _ _ _ _ _ Selected))
  as [s [m [D [End [Safe [WF [G [M [_ [C Sign]]]]]]]]]].
 exists (Trace r q s m);split;[unfold observe;rewrite A;cbn [bind];fold p0 k0;rewrite B;cbn [bind];now rewrite D|].
 constructor;cbn [candidate at_store selected];try assumption;now exists k.
Qed.
