From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.MemoryGeometry memory.FlatMemory.
From Machine Require execution.MaskTransfer.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchDecode KeySquare NativeScale.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderFinish FinishProduct RootAccept RootCandidate RootAdjusted
 RootSign RowProduct ReturnedPoint ExtendedPoint.
Local Open Scope Z_scope.

Record trace:=Trace { test:cursor; validity:cursor; test_masks:MaskTransfer.bank; raw:cursor;
 chosen:cursor; signed:cursor; masks:MaskTransfer.bank; returned:cursor }.
Definition execute bias p bank:=bind (FinishProduct.finish bias p) (fun cmp=>
 bind (RootAccept.execute bias cmp bank) (fun '(valid,bits)=>bind (RootCandidate.execute bias valid) (fun candidate=>
 bind (RootAdjusted.execute bias candidate bits) (fun '(root,k)=>bind (RootSign.execute bias root k) (fun '(signed,m)=>
 option_map (Trace cmp valid bits candidate root signed m) (ReturnedPoint.execute bias signed)))))).
Record post sig pol bias e p t : Prop:=Post {
 test_result:FinishProduct.post sig pol bias e p (test t);
 raw_result:RootCandidate.result sig pol bias e (validity t) (raw t);
 choice:exists ks,RootAdjusted.result pol bias e (raw t) (test_masks t) (chosen t) ks;
 coordinates:ReturnedPoint.result sig pol bias e (signed t) (returned t);
 numerator:forall j i,(i<5)%nat -> vectors(machine(validity t)) j i=row (machine(test t)) (point e sig) j i;
 sign:forall j i,(j<8)%nat -> (i<5)%nat -> vectors(machine(signed t)) j i=RootSign.adjusted (machine(chosen t)) j i;
 mask_byte:0<=regs(machine(returned t)) 0%nat<256;
 mask_bit:forall j,(j<8)%nat -> Z.testbit (regs(machine(returned t)) 0%nat) (Z.of_nat j)=RootAccept.bits sig e (machine(test t)) j /\
    test_masks t 4%nat j=Radix51Digits.high_test (vectors(machine(test t)) j) (-1);
 callee_registers:forall r,r<>0%nat -> r<>4%nat -> r<>8%nat -> r<>10%nat -> regs(machine(returned t)) r=regs(machine p) r;
 factor_pointer:regs(machine(validity t)) 6%nat=regs(machine(test t)) 6%nat;
 validity_memory:mem(machine(validity t))=mem(machine(test t));
 sign_register:regs(machine(chosen t)) 9%nat=regs(machine p) 9%nat;
 y_memory:preserved (span (point e sig+320) 320) (mem(machine(test t))) (mem(machine(signed t)));
 frame:preserved (ExtendedPoint.protected sig pol e) (mem(machine p)) (mem(machine(returned t)))
}.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem checked sig pol bias e p bank : placement e -> loaded pol bias (mem e) (writable e) ->
 DecoderFinish.entry sig pol bias e p -> exists t,execute bias p bank=Some t /\ post sig pol bias e p t.
Proof.
 intros P I Entry;destruct(FinishProduct.from_entry sig pol bias e p P I Entry) as [cmp [A Test]].
 destruct Entry as [_ [_ [_ [SP [DI [SI [Link _]]]]]]].
 destruct Test as [PC [Acc [W [G [Keep [C Math]]]]]].
 destruct(RootAccept.checked sig pol bias e cmp bank P I PC Acc ltac:(rewrite G by discriminate;exact DI)
    (fun j=>C 1%nat j ltac:(lia))) as [v [k [B [At [Safe [_ [Memory [Reg [U [High [Byte Bits]]]]]]]]]]].
 pose proof(RootAccept.words _ _ _ _ _ W B) as WV.
 assert (R0:forall r,r<>8%nat -> r<>10%nat -> regs(machine v) r=regs(machine p) r) by
   (intros r R N;rewrite Reg,G by assumption;reflexivity).
 assert (CV:RowProduct.constants(machine v)) by (intros i j N;rewrite High by lia;apply C,N).
 destruct(RootCandidate.checked sig pol bias e v P I At Safe WV ltac:(rewrite R0 by discriminate;exact SP)
  ltac:(rewrite R0 by discriminate;exact DI) ltac:(rewrite R0 by discriminate;exact SI) CV)
  as [x [D X]].
 assert (RX:forall r,r<>8%nat -> regs(machine x) r=regs(machine v) r) by
  (intros r R;rewrite (RootCandidate.regs_after _ _ _ _ _ _ X),(proj2(Nat.eqb_neq r 8) R);reflexivity).
 destruct(RootAdjusted.checked sig pol bias e x k P I (RootCandidate.next_call _ _ _ _ _ _ X)
  (RootCandidate.writes _ _ _ _ _ _ X) (RootCandidate.words _ _ _ _ _ _ X)
  ltac:(rewrite RX,R0 by discriminate;exact SP) ltac:(rewrite RX,R0 by discriminate;exact DI)
  (RootCandidate.high _ _ _ _ _ _ X)
  ltac:(intros j i J N;destruct(RootCandidate.live_x _ _ _ _ _ _ X j i J N) as [L M];exact (eq_trans M (eq_sym L))))
  as [r [kr [F Adjust]]].
 destruct(RootSign.checked pol bias e r kr I (RootAdjusted.next _ _ _ _ _ _ _ Adjust)
  (RootAdjusted.writes _ _ _ _ _ _ _ Adjust) (RootAdjusted.words _ _ _ _ _ _ _ Adjust) (RootAdjusted.high _ _ _ _ _ _ _ Adjust))
  as [s [ms [H [End [Paid [WS [GS [MS [_ [CS Signed]]]]]]]]]].
 set (st:=link_slot pol e) in *;set (a:=point e sig) in *.
 assert (GSV:forall n,n<>8%nat -> regs(machine s) n=regs(machine v) n)
   by (intros n N;rewrite GS,(RootAdjusted.gprs _ _ _ _ _ _ _ Adjust),RX by exact N;reflexivity).
 assert (M0:preserved (fun z=>~(st-24<=z<st) /\ ~(a+960<=z<a+1280)) (mem(machine p)) (mem(machine s))).
 { intros z [Stack Point];rewrite MS,(RootAdjusted.frame _ _ _ _ _ _ _ Adjust z Stack),
     (RootCandidate.frame _ _ _ _ _ _ X z (conj Stack Point)),Memory;exact (Keep z Stack). }
 assert (Back:read_word (mem(machine s)) st=base bias+DecoderFinish.return_offset sig).
 { rewrite <-Link;apply preserved_read with (outside:=fun z=>~(st-24<=z<st) /\ ~(a+960<=z<a+1280));[exact M0|].
   intros n N;change (0<=n<8) in N;pose proof(depth pol e);fold st in H0;destruct(scratch_stack _ P);
   unfold disjoint,a,point,point_offset in *;destruct sig;lia. }
 destruct(ReturnedPoint.checked sig pol bias e s P I End Paid WS
   ltac:(rewrite GSV,R0 by discriminate;exact SP) ltac:(rewrite GSV,R0 by discriminate;exact DI) CS Back) as [q [Last Out]].
 assert (Mask:regs(machine q) 0%nat=regs(machine v) 10%nat)
   by (rewrite (ReturnedPoint.mask _ _ _ _ _ _ Out),GSV by discriminate;apply Z.mod_small;lia).
 exists(Trace cmp v k x r s ms q);split.
 - unfold execute;rewrite A;cbn [bind];rewrite B;cbn [bind];rewrite D;cbn [bind];rewrite F;cbn [bind];rewrite H;cbn [bind];now rewrite Last.
 - constructor;cbn [test validity raw chosen signed returned test_masks].
   + exact (conj PC (conj Acc (conj W (conj G (conj Keep (conj C Math)))))).
   + exact X.
   + now exists kr.
   + exact Out.
   + exact U.
   + exact Signed.
   + now rewrite Mask.
   + intros j J;rewrite Mask;apply Bits,J.
   + intros n Z Four Eight Ten;rewrite (ReturnedPoint.preserved_regs _ _ _ _ _ _ Out),GSV,R0 by assumption;reflexivity.
   + apply Reg;discriminate.
   + exact Memory.
   + rewrite (RootAdjusted.gprs _ _ _ _ _ _ _ Adjust),RX,R0 by discriminate;reflexivity.
   + intros z Y;assert (Apart:~(st-24<=z<st)).
     { pose proof(depth pol e);destruct(scratch_stack _ P);unfold st,span,point,point_offset,disjoint in *;destruct sig;lia. }
     rewrite (M0 z),Keep;[reflexivity|exact Apart|split;[exact Apart|unfold a,span in *;lia]].
   + intros z Protected;rewrite (ReturnedPoint.untouched _ _ _ _ _ _ Out z Protected);apply M0;unfold ExtendedPoint.protected in Protected;fold a st in Protected;lia.
Qed.
End Iteration.
