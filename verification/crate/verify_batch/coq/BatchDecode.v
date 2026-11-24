From Coq Require Import List ZArith Lia.
From Machine Require Import execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.MappedFetch memory.ByteMemory memory.FlatMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.Decode Require DecoderBytes.
From Ed25519Simd.PrepareChunk Require CommonBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Rows Return LoadedImage ScalarInputs BatchScalar.
From Ed25519Simd.VerifyBatch Require PrepareCopies TailCopy.
Local Open Scope Z_scope.

Definition readable e := forall j sig,(j<8)%nat ->
 let p:=encoding_ptr e j sig in fits64 p 32 /\ forall x,p<=x<p+32 -> ~writable e x.
Definition enter bias p := segment (bias+PrepareNative.common) CommonBytes.symbol_bytes 88 p.
Definition observe pol bias pc text e c ks :=
 bind (BatchScalar.observe pol bias (bias+pc) text e c ks) (fun p=>
 if regs(machine p) 0%nat mod 2^32=?0 then None else enter bias p).
Definition entry pol bias e p :=
 ip p=bias+DecoderBytes.address /\ accounted e (writable e) p /\
 regs(machine p) 7%nat=scratch e+1024 /\ regs(machine p) 6%nat=scratch e /\ regs(machine p) 2%nat=2 /\
 regs(machine p) 4%nat=common_top pol e-112 /\
 read_word (mem(machine p)) (common_top pol e-112)=word(bias+PrepareNative.common+142) /\
 PrepareCopies.staged (mem e) (mem(machine p)) (scratch e) (encoding_ptr e) 8.

Lemma decode_in pol : In (DecoderBytes.address,DecoderBytes.symbol_bytes) (children pol).
Proof. apply in_or_app;left;do 5 right;left;reflexivity. Qed.

Theorem from_scalar pol bias pc text e c ks p :
 placement e -> loaded pol bias (mem e) (writable e) -> readable e ->
 BatchScalar.observe pol bias (bias+pc) text e c ks=Some p -> BatchScalar.post pol bias (bias+pc) e p ->
 copy_ready e (machine p) -> regs(machine p) 0%nat mod 2^32<>0 ->
 exists q,observe pol bias pc text e c ks=Some q /\ entry pol bias e q.
Proof.
 intros Place Image Inputs Prefix [PC [SP [Acc _]]] [Bytes [Ptr [BX Rows]]] Live.
 set (frame:=common_top pol e-104) in *;set (dst:=scratch e) in *.
 set (table:=Rows.frame e+512) in *.
 destruct(stack_ok _ Place) as [[Lo Hi] _];destruct(scratch_ok _ Place) as [[D U] Al].
 assert (Frame:sp e-1200<=frame<sp e-1000) by (unfold frame,common_top,Rows.frame,sp;destruct pol;lia).
 assert (T:fits64 table 128) by (unfold table,Rows.frame,sp,fits64 in *;lia).
 assert (Apart:disjoint dst 512 table 128) by
   (destruct (scratch_stack _ Place);unfold disjoint,dst,table,Rows.frame,sp in *;lia).
 assert (Aligned:dst mod 32=0).
 { unfold dst;apply Z.mod_divide in Al as [u Eq];[rewrite Eq;apply Z.mod_divide;[lia|exists (2*u);ring]|lia]. }
 assert (Ranges:forall j (sig:bool),(j<8)%nat ->
   fits64 (encoding_ptr e j sig) 32 /\ disjoint dst 512 (encoding_ptr e j sig) 32).
 { intros j sig J;destruct(Inputs j sig J) as [Fit Safe];split;[exact Fit|].
   apply ScalarInputs.apart;[lia|lia|]. intros x X Touch;apply (Safe x X);right;left;unfold span;fold dst;lia. }
 assert (Original:PrepareCopies.source_view (mem e) (mem(machine p)) (encoding_ptr e)).
 { intros j sig k J K;rewrite (proj2 Acc);apply (WriteTrace.frame _ _ (proj1 Acc)),(proj2 (Inputs j sig J));lia. }
 pose proof (BatchScalar.mapped_word _ _ _ Image _ _ (decode_in _) ltac:(vm_compute;reflexivity)) as Target.
 destruct (PrepareCopies.to_decoder bias frame dst table (mem e) (encoding_ptr e) (machine p) (carry p)
    Live SP BX Rows ltac:(unfold fits64;lia) Aligned T Apart ltac:(unfold word64;lia) Target
    ltac:(destruct (scratch_stack _ Place);unfold disjoint,dst in *;lia)
    Ranges Bytes Ptr Original) as [t [ws [R [[IP [DI [SI [DX [Top [Ret Data]]]]]] Writes]]]].
 destruct (mapped_now _ _ _ Image _ _ _ Acc (in_common _)) as [Map Sep].
 assert (Safe:confined (writable e) ws).
 { eapply Forall_impl;[|exact Writes];intros w H x X;destruct (H x X);[right;left|left];unfold span;fold dst;lia. }
 pose proof (at_segment _ _ _ _ _ _ 65 _ _ Acc PC Map Sep R Safe) as [Next A].
 eexists;split.
 - unfold observe;rewrite Prefix;cbn [bind];rewrite (proj2 (Z.eqb_neq _ _) Live);exact Next.
 - split;[|split;[exact A|]].
   + cbn [LinkedRun.finish ip];unfold absolute;rewrite IP;unfold PrepareCopies.common,PrepareCopies.decoder,PrepareNative.common;ring.
   + cbn [LinkedRun.finish machine];split;[exact DI|split;[exact SI|split;[exact DX|]]].
     replace (common_top pol e-112) with (frame-8) by (unfold frame;ring).
     exact (conj Top (conj Ret Data)).
Qed.
