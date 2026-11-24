From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordBounds execution.WordSemantics execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute execution.VectorProcedure
 memory.ByteMemory memory.FlatMemory memory.MemoryGeometry memory.WriteTrace.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd.Decode Require Kernels Power.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare NativeScale.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderProduct DecoderKernel DecoderFinish FinishSquare NativeWords.
Import ListNotations. Local Open Scope Z_scope.

Definition pointer_code:list line:=[(940,7%nat,LeaG 8 (Address 7 None 960))].
Lemma bytes : linked text pointer_code /\
 ScalarBytes.decode (skipn 947 text)=Some(5%nat,CallRelative(0xa57-952)).
Proof. repeat split;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition pointer bias:=segment (base bias) text 1.
Definition finish bias:=then_run (FinishSquare.evaluate bias) (then_run (pointer bias) (DecoderProduct.multiply_call bias)).
Definition candidate x uv:=let h:=Power.apply_kernel DecoderProduct.kernel Kernels.Square x x in
 Power.apply_kernel DecoderProduct.kernel Kernels.Multiply h uv.
Definition post sig pol bias e p q:=let st:=link_slot pol e in
 ip q=base bias+952 /\ accounted e (writable e) q /\ well_formed(machine q) /\
 (forall r,r<>8%nat -> regs(machine q) r=regs(machine p) r) /\
 preserved (fun x=>~(st-24<=x<st)) (mem(machine p)) (mem(machine q)) /\
 (forall i j,(i<4)%nat -> vectors(machine q) j (28+i)%nat=DecoderFrame.constant i) /\
 forall j i,(j<8)%nat -> (i<5)%nat -> vectors(machine q) j i=
 candidate (FinishSquare.operand sig pol e (machine p) j) (row (machine p) (point e sig+960) j) i.

Theorem from_entry sig pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 DecoderFinish.entry sig pol bias e p -> exists q,finish bias p=Some q /\ post sig pol bias e p q.
Proof.
 intros P I E;destruct(FinishSquare.from_entry _ _ _ _ _ P I E) as [sq [Square [PC [Acc [W [G [K [High Squares]]]]]]]].
 destruct E as [_ [_ [_ [Top [Dst _]]]]].
 set (o:=base bias) in *;set (z:=machine sq) in *;set (a:=point e sig+960).
 assert (SP:regs z 4%nat=link_slot pol e) by (rewrite G;exact Top).
 destruct(scratch_ok _ P) as [[L H] Align];pose proof(depth pol e) as Depth;destruct(Return.stack_ok _ P) as [[Lo Hi] _].
 assert (Fit:fits64 a 320) by (unfold a,point,point_offset,fits64;destruct sig;lia).
 assert (Al:a mod 64=0) by (unfold a;replace 960 with (15*64) by ring;rewrite Z.mod_add by lia;apply point_aligned,Align).
 assert (Dis:forall x,a<=x<a+320 -> ~(link_slot pol e-24<=x<link_slot pol e)).
 { intros x X;destruct(scratch_stack _ P);unfold disjoint,a,point,point_offset in *;destruct sig;lia. }
 set (v:=set z 8 a).
 assert (Lea:run 1 (ScalarBytes.fetch o text) (State (Running 940) z (LinkedRun.carry sq))=
    Some(State (Running 947) v (LinkedRun.carry sq),[])).
 { apply (checked _ _ _ (proj1 bytes));cbn [pointer_code follow step loc cf cpu_state effective option_map];
   rewrite G,Dst,Z.add_0_r,word_fits by (unfold fits64,word64,a in *;lia);reflexivity. }
 destruct(mapped_now _ _ _ I _ _ _ Acc (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ _ o text 1 940 _ _ Acc PC Map Sep Lea (Forall_nil _)) as [Next Paid].
 set (mid:=LinkedRun.finish o sq (State (Running 947) v (LinkedRun.carry sq),[])) in *;set (s:=push v (o+952)).
 set (args:=DecoderProduct.arguments s).
 assert (R8:regs s 8%nat=a) by reflexivity.
 assert (Need:DecoderProduct.readable args s) by (split;[now rewrite R8|split;[now rewrite R8|reflexivity]]).
 destruct(DecoderProduct.call_at pol bias e 947 args P I ltac:(lia) ltac:(lia) (proj2 bytes) mid Need eq_refl Paid
   ltac:(change (sp e-16384+24<=regs z 4%nat<=sp e);rewrite SP;lia)) as [q [Call [End Done Reg Keep Value]]].
 assert (WF:well_formed(machine q)) by (eapply (proj1(NativeWords.kernels bias));[|exact Call];eapply segment_wf;[exact W|exact Next]).
 assert (Args:forall j i,(j<8)%nat -> (i<5)%nat ->
  args j i=Power.apply_kernel DecoderProduct.kernel Kernels.Square (FinishSquare.operand sig pol e (machine p) j)
      (FinishSquare.operand sig pol e (machine p) j) i /\ args j (5+i)%nat=row (machine p) a j i).
 { intros j i J N;unfold args,DecoderProduct.arguments;
   rewrite (proj2(Nat.leb_gt 5 i) ltac:(lia)),(proj2(Nat.leb_le 5 (5+i)) ltac:(lia)),
     (proj2(Nat.ltb_lt (5+i) 10) ltac:(lia));cbn [andb];split;[apply Squares;assumption|].
   replace (5+i-5)%nat with i by lia;unfold DecoderProduct.rhs_at,row;rewrite R8.
   apply preserved_read with (outside:=fun x=>a<=x<a+320).
   - intros x X;change (store_word (mem z) (word(regs z 4%nat-8)) (o+952) x=mem(machine p) x).
     rewrite SP,word_fits by (unfold word64;lia);unfold store_word;rewrite write_outside by (specialize(Dis x X);lia).
     apply K;specialize(Dis x X);lia.
   - intros k B;change (0<=k<8) in B;lia. }
 assert (Consts:forall j i,(i<4)%nat -> args j (28+i)%nat=DecoderFrame.constant i).
 { intros j i N;unfold args,DecoderProduct.arguments;rewrite (proj2(Nat.ltb_ge (28+i) 10) ltac:(lia)),andb_false_r;apply High,N. }
 exists q;split;[unfold finish,then_run,pointer;fold o;rewrite Square;cbn [bind];rewrite Next;exact Call|].
 split;[exact End|split;[exact Done|split;[exact WF|split]]].
 - intros r N;rewrite Reg;change (put (regs z) 8 a r=regs(machine p) r);unfold put;rewrite (proj2(Nat.eqb_neq 8 r) ltac:(lia));apply G.
 - split.
   + intros x X;transitivity (mem z x);[apply Keep;change (~(regs z 4%nat-24<=x<regs z 4%nat));now rewrite SP|apply K;lia].
   + split.
     * intros i j N;rewrite Value;destruct((proj2 DecoderProduct.multiplication) no_read no_read (args j) (args j) ltac:(reflexivity)) as [_ Survive];
       rewrite Survive by lia;apply Consts,N.
     * intros j i J N;rewrite (Value j i);unfold candidate.
       exact (DecoderProduct.lane_product (args j) _ _ (fun k B=>Args j k J B) (Consts j) i N).
Qed.
