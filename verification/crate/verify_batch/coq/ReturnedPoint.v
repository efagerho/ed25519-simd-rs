From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.VectorProcedure memory.ByteMemory memory.MemoryGeometry.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchDecode KeySquare.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderFinish RowProduct ExtendedPoint FinishRet.
Local Open Scope Z_scope.

Definition execute bias:=then_run (ExtendedPoint.execute bias) (FinishRet.execute bias).
Record result sig pol bias e p q : Prop:=Result {
 point_before_return:exists t,ExtendedPoint.result sig pol bias e p t /\ mem(machine q)=mem(machine t);
 resume:ip q=base bias+DecoderFinish.return_offset sig;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 stack:regs(machine q) 4%nat=link_slot pol e+8;
 mask:regs(machine q) 0%nat=regs(machine p) 10%nat mod 2^32;
 preserved_regs:forall r,r<>0%nat -> r<>4%nat -> r<>8%nat -> regs(machine q) r=regs(machine p) r;
 high:RowProduct.constants(machine q);
 untouched:preserved (ExtendedPoint.protected sig pol e) (mem(machine p)) (mem(machine q))
}.

Theorem checked sig pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 ip p=base bias+1299 -> accounted e (writable e) p -> well_formed(machine p) ->
 regs(machine p) 4%nat=link_slot pol e -> regs(machine p) 7%nat=point e sig -> RowProduct.constants(machine p) ->
 read_word (mem(machine p)) (link_slot pol e)=base bias+DecoderFinish.return_offset sig ->
 exists q,execute bias p=Some q /\ result sig pol bias e p q.
Proof.
 intros P I PC Acc W SP DI C Link;set (st:=link_slot pol e) in *;set (a:=point e sig) in *.
 destruct(ExtendedPoint.checked sig pol bias e p P I PC Acc W SP DI C) as [t [T R]].
 assert (Slot:read_word (mem(machine t)) st=base bias+DecoderFinish.return_offset sig).
 { rewrite <-Link;apply preserved_read with (outside:=ExtendedPoint.protected sig pol e);[exact (ExtendedPoint.frame _ _ _ _ _ _ R)|].
   intros k K;change (0<=k<8) in K;pose proof(depth pol e);fold st in H;
   destruct(scratch_stack _ P);unfold ExtendedPoint.protected,FlatMemory.disjoint,point,point_offset in *;destruct sig;lia. }
 destruct(FinishRet.checked sig pol bias e t P I (ExtendedPoint.next _ _ _ _ _ _ R) (ExtendedPoint.writes _ _ _ _ _ _ R)
  (ExtendedPoint.words _ _ _ _ _ _ R) ltac:(rewrite (ExtendedPoint.gprs _ _ _ _ _ _ R);exact SP) Slot)
  as [q [Ret [End [Done [WF [Stack [EAX [G [M [V _]]]]]]]]]].
 exists q;split;[unfold execute,then_run;rewrite T;exact Ret|constructor].
 - exists t;auto.
 - exact End.
 - exact Done.
 - exact WF.
 - exact Stack.
 - rewrite EAX,(ExtendedPoint.gprs _ _ _ _ _ _ R);reflexivity.
 - intros r Z F B;rewrite G,(ExtendedPoint.gprs _ _ _ _ _ _ R),(proj2(Nat.eqb_neq r 8) B) by assumption;reflexivity.
 - intros i j N;rewrite V;exact (ExtendedPoint.constants_after _ _ _ _ _ _ R i j N).
 - intros x X;rewrite M;apply (ExtendedPoint.frame _ _ _ _ _ _ R),X.
Qed.
