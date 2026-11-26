From Curve25519 Require Radix51Digits.
From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordBounds execution.WordSemantics execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.MappedFetch execution.VectorProcedure memory.ByteMemory memory.FlatMemory memory.MemoryGeometry.
From Machine Require execution.MaskTransfer execution.MaskedResult.
From Ed25519Simd.Decode Require Decode Kernels Power.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare NativeScale.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderKernel DecoderProduct RowProduct RootMultiply SetupValues MaskSegment.
Import ListNotations. Local Open Scope Z_scope.
Module MR:=MaskedResult.

Definition select:=MR.Invert 4 4 :: MR.rows 0 4 7 960 5.
Definition bytes:=firstn 39 (skipn 1124 text).
Lemma image:MR.assemble 1124 select=Some bytes /\ length bytes=39%nat.
Proof. split;vm_compute;reflexivity. Qed.
Definition execute bias p bank:=bind (RootMultiply.execute bias p) (fun q=>MR.execute (base bias) select q bank).
Definition adjusted s (bank:MaskTransfer.bank) j:=if bank 4%nat j then
 Power.apply_kernel DecoderProduct.kernel Kernels.Multiply (vectors s j) Radix51Digits.sqrt_limbs else vectors s j.

Record result pol bias e p bank q (out:MaskTransfer.bank):Prop:=Result {
 next:ip q=base bias+1163;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 gprs:forall r,regs(machine q) r=regs(machine p) r;
 frame:preserved (fun x=>~(link_slot pol e-24<=x<link_slot pol e)) (mem(machine p)) (mem(machine q));
 high:RowProduct.constants(machine q);
 root:forall j i,(j<8)%nat -> (i<5)%nat -> vectors(machine q) j i=adjusted (machine p) bank j i;
 bank_after:out=MR.set_mask bank 4 16 (fun j=>negb(bank 4%nat j))
}.

Theorem checked sig pol bias e p bank : placement e -> loaded pol bias (mem e) (writable e) ->
 ip p=base bias+1119 -> accounted e (writable e) p -> well_formed(machine p) ->
 regs(machine p) 4%nat=link_slot pol e -> regs(machine p) 7%nat=point e sig -> RowProduct.constants(machine p) ->
 (forall j i,(j<8)%nat -> (i<5)%nat -> row (machine p) (point e sig+960) j i=vectors(machine p) j i) ->
 exists q out,execute bias p bank=Some(q,out) /\ result pol bias e p bank q out.
Proof.
 intros P I PC Acc W SP DI C Saved;set (o:=base bias) in *;set (a:=point e sig+960).
 pose proof(depth pol e) as Depth;destruct(scratch_ok _ P) as [[L H] Al].
 destruct(RootMultiply.called _ _ _ P I p Logic.I PC Acc ltac:(change (sp e-16384+24<=regs(machine p) 4%nat<=sp e);rewrite SP;lia))
   as [u [Call [At Safe Reg Keep Times]]].
 pose proof(RootMultiply.words _ _ _ W Call) as WU.
 destruct(RootMultiply.multiplied _ _ C Times) as [CU Alternate].
 set (ks:=MR.set_mask bank 4 16 (fun j=>negb(bank 4%nat j))).
 assert (Align:a mod 64=0) by (unfold a;replace 960 with (15*64) by ring;rewrite Z.mod_add by lia;apply point_aligned,Al).
 destruct(MR.load_rows o 5 0 4 7 960 a (machine u) ks ltac:(rewrite Reg,DI;reflexivity)
   Align ltac:(unfold a,point,point_offset;destruct sig;lia)
   ltac:(unfold a,point,point_offset;destruct sig;change (Z.of_nat 5) with 5;lia))
   as [v [Rows [G [M [Value Other]]]]].
 assert (Eval:MR.evaluate o (machine u) bank select=Some(v,ks)) by exact Rows.
 destruct(MaskSegment.checked pol bias e 1124 39 select u bank v ks I ltac:(lia) ltac:(change (1163<2984);lia)
   (proj2 image) (proj1 image) At Safe WU Eval) as [q [Pick [V [End [Done [WF _]]]]]].
 assert (Original:forall j i,(j<8)%nat -> (i<5)%nat -> row (machine u) a j i=vectors(machine p) j i).
 { intros j i J N;transitivity(row (machine p) a j i);[|exact (Saved j i J N)].
   apply SetupValues.keep_row with (protect:=fun x=>~(link_slot pol e-24<=x<link_slot pol e));[| |exact J|exact N].
   - intros x X;apply Keep;now rewrite SP.
   - intros x X;destruct(scratch_stack _ P);unfold disjoint,a,point,point_offset in *;destruct sig;lia. }
 exists q,ks;split;[unfold execute;rewrite Call;exact Pick|constructor].
 - exact End.
 - exact Done.
 - exact WF.
 - intro r;rewrite V,G;apply Reg.
 - intros x X;rewrite V,M;apply Keep;now rewrite SP.
 - intros i j N;rewrite V,Other by lia;apply CU,N.
 - intros j i J N;rewrite V;cbn [Nat.add] in Value;rewrite (Value i j N);unfold adjusted,ks,MR.set_mask,put;cbn [Nat.eqb];rewrite (proj2(Nat.ltb_lt j 16) ltac:(lia)).
   destruct(bank 4%nat j);cbn [andb orb negb];[apply Alternate,N|apply Original;assumption].
 - reflexivity.
Qed.
