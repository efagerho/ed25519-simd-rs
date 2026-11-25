From Coq Require Import List ZArith Lia.
From Machine Require Import execution.WordSemantics execution.WordBounds execution.LinkedCalls memory.FlatMemory memory.MemoryGeometry.
From Ed25519Simd.CachedAdd Require CachedAddABI CachedAddMemory ObjectBytes.
From Ed25519Simd.LadderStep Require LinkedBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require TableFrame TableProduct ScalarInputs.
Import ListNotations. Local Open Scope Z_scope.

Definition origin:=LadderStep.LinkedBytes.cached_pc.
Definition text:=CachedAdd.ObjectBytes.symbol_bytes.
Definition size:=Z.of_nat(length text).
Definition back bias:=TableFrame.base bias+1974.
Definition stage pol e:=TableProduct.frame pol e.
Definition regions pol e r:=match r with
 | O=>stage pol e-1344 | S O=>TableEntry.point e | _=>stage pol e end.
Definition layout pol bias e:=Placement (regions pol e) (bias+origin) (back bias).
Definition pad:=48.
Lemma image pol:In (origin,text) (children pol).
Proof. apply in_or_app;left;do 15 right;left;reflexivity. Qed.
Lemma stack pol e: sp e-2500<=stage pol e /\ stage pol e+960<=sp e /\ stage pol e mod 64=0.
Proof.
 unfold stage,TableProduct.frame,KeyTable.Frame.staging,KeyTable.Frame.allocation;change KeyTable.Frame.saved_size with 48.
 split;[|split].
 1,2: unfold KeyTable.Frame.align64,TableEntry.frame,BatchScalar.common_top,Rows.frame,sp;
    pose proof(Z.mod_pos_bound (TableEntry.frame pol e-48) 64 ltac:(lia));unfold TableEntry.frame,BatchScalar.common_top,Rows.frame,sp in *;destruct pol;lia.
 rewrite Zminus_mod,KeyTable.Frame.aligned;reflexivity.
Qed.
Lemma continuation pol bias e : loaded pol bias (mem e) (writable e) -> word64(back bias).
Proof.
 intros I;destruct(proj1(symbols _ _ _ _ I _ _ (TableEntry.image pol))) as [L H].
 change (0<=TableFrame.base bias) in L;change (TableFrame.base bias+2280<=2^64) in H;unfold back,word64;lia.
Qed.
Lemma entry_sp pol bias e : PointFrame.entry_rsp (layout pol bias e) pad=stage pol e-8.
Proof. unfold PointFrame.entry_rsp,layout,regions,pad,PointFrame.scratch;cbn [FlatMemory.origin];ring. Qed.
Lemma valid pol bias e : placement e -> loaded pol bias (mem e) (writable e) ->
 CachedAddMemory.valid_placement true (layout pol bias e) size pad.
Proof.
 intros P I;set (s:=stage pol e);set (pt:=TableEntry.point e).
 destruct(stack pol e) as [SL [SH Al]];fold s in SL,SH,Al;destruct(stack_ok _ P) as [[L H] _].
 destruct(scratch_ok _ P) as [[Low High] Align];pose proof(scratch_stack _ P) as Apart.
 pose proof(proj1(symbols _ _ _ _ I _ _ (image pol))) as Fit;change (fits64 (bias+origin) size) in Fit.
 assert (Part:forall a n,0<n -> (forall x,a<=x<a+n -> writable e x) -> disjoint a n (bias+origin) size).
 { intros a n Pos Area;apply ScalarInputs.apart;[exact Pos|vm_compute;reflexivity|intros x Code X].
   apply (immutable _ _ _ _ I x);[left;exists origin,text;split;[apply image|exact Code]|apply Area,X]. }
 assert (Point:disjoint pt 1280 (bias+origin) size) by (apply Part;[lia|intros;right;left;unfold pt,TableEntry.point,span in *;lia]).
 assert (Scratch:disjoint (s-1344-16) (1312+48) (bias+origin) size) by (apply Part;[lia|intros;left;unfold span;lia]).
 assert (Cache:disjoint s 960 (bias+origin) size) by (apply Part;[lia|intros;left;unfold span;lia]).
 assert (PA:pt mod 64=0) by (unfold pt,TableEntry.point;replace (scratch e+1024) with (scratch e+16*64) by ring;now rewrite Z.mod_add by lia).
 assert (SA:(s-1344) mod 64=0) by (replace (s-1344) with (s+(-21)*64) by ring;now rewrite Z.mod_add by lia).
 pose proof(continuation _ _ _ I) as Back.
 assert (Away:~(bias+origin<=back bias<bias+origin+size)).
 { assert (Order:origin+size<=TableEntry.origin+1974) by (vm_compute;discriminate || reflexivity).
   unfold back,TableFrame.base;lia. }
 unfold CachedAddMemory.valid_placement,PointFrame.point_placement,layout,regions,PointFrame.scratch,PointFrame.point,
    CachedAddABI.cached,CachedAddABI.cache_length,pad;cbn [FlatMemory.origin caller_pc code_base].
 fold s pt;assert (Pad:PointFrame.permitted_padding 48) by (right;right;right;left;reflexivity).
 repeat split;try assumption.
 all: unfold pt,TableEntry.point,fits64,word64,disjoint in *;lia.
Qed.
