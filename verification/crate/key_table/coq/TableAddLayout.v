From Coq Require Import List ZArith Lia.
From Machine Require Import execution.WordSemantics execution.WordBounds execution.LinkedCalls memory.FlatMemory memory.MemoryGeometry.
From Ed25519Simd.CachedAdd Require CachedAddABI CachedAddMemory ObjectBytes.
From Ed25519Simd.KeyTable Require CachedBytes.
From Ed25519Simd.KeyTable Require TableProduct.
From Ed25519Simd.KeyTable Require Import CallLayout.
Import ListNotations. Local Open Scope Z_scope.

Definition origin:=CachedBytes.address.
Definition text:=CachedAdd.ObjectBytes.symbol_bytes.
Definition size:=Z.of_nat(length text).
Definition back bias:=CallLayout.base bias+1974.
Definition regions e r:=match r with
 | O=>CallLayout.stage e-1344 | S O=>CallLayout.point_ptr e | _=>CallLayout.stage e end.
Definition layout bias e:=Placement (regions e) (bias+origin) (back bias).
Definition pad:=48.
Lemma image:In(origin,text) children.
Proof. exact cached_in. Qed.
Lemma continuation (root:cpu) bias e : loaded root bias e -> word64(back bias).
Proof.
 intros I;destruct(proj1(symbols _ _ _ I _ _ builder_in)) as [L H].
 change (0<=CallLayout.base bias) in L;change (CallLayout.base bias+2280<=2^64) in H;unfold back,word64;lia.
Qed.
Lemma entry_sp bias e : PointFrame.entry_rsp (layout bias e) pad=CallLayout.stage e-8.
Proof. unfold PointFrame.entry_rsp,layout,regions,pad,PointFrame.scratch;cbn [FlatMemory.origin];ring. Qed.
Lemma valid (root:cpu) bias e : placement e -> loaded root bias e ->
 CachedAddMemory.valid_placement true (layout bias e) size pad.
Proof.
 intros P I;set (s:=CallLayout.stage e);set (pt:=CallLayout.point_ptr e).
 destruct(CallLayout.depth e P) as [SL [SH Al]];fold s in SL,SH,Al;destruct(stack_fit _ P) as [L H].
 destruct(point_fit _ P) as [Low High];pose proof(CallLayout.point_stack _ P) as Apart.
 destruct(symbols _ _ _ I _ _ image) as [Fit [_ Sep]].
 change (fits64 (bias+origin) size) in Fit.
 assert (Part:forall a n,0<n -> (forall x,a<=x<a+n -> writable e x) -> disjoint a n (bias+origin) size).
 { intros a n Pos Area;apply apart;[exact Pos|vm_compute;reflexivity|intros x Code X;exact (Sep x Code (Area x X))]. }
 assert (Point:disjoint pt 1280 (bias+origin) size) by (apply Part;[lia|intros;apply (permits _ P);right;left;assumption]).
 assert (Scratch:disjoint (s-1344-16) (1312+48) (bias+origin) size) by
   (apply Part;[lia|intros;apply (permits _ P);left;unfold span;lia]).
 assert (Cache:disjoint s 960 (bias+origin) size) by
   (apply Part;[lia|intros;apply (permits _ P);left;unfold span;lia]).
 assert (PA:pt mod 64=0) by apply (point_alignment _ P).
 assert (SA:(s-1344) mod 64=0) by (replace (s-1344) with (s+(-21)*64) by ring;now rewrite Z.mod_add by lia).
 pose proof(continuation _ _ _ I) as Back.
 assert (Away:~(bias+origin<=back bias<bias+origin+size)).
 { assert (Order:origin+size<=CallLayout.origin+1974) by (vm_compute;discriminate || reflexivity).
   unfold back,CallLayout.base;lia. }
 unfold CachedAddMemory.valid_placement,PointFrame.point_placement,layout,regions,PointFrame.scratch,PointFrame.point,
    CachedAddABI.cached,CachedAddABI.cache_length,pad;cbn [FlatMemory.origin caller_pc code_base].
 fold s pt;assert (Pad:PointFrame.permitted_padding 48) by (right;right;right;left;reflexivity).
 repeat split;try assumption.
 all: unfold pt,fits64,word64,disjoint in *;lia.
Qed.
