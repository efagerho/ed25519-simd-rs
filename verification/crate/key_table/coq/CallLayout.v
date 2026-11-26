From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds execution.MappedFetch
 execution.VectorProcedure memory.FlatMemory memory.MemoryGeometry.
From Ed25519Simd.Decode Require DecoderBytes HelperBytes.
From Ed25519Simd.KeyTable Require Frame ObjectBytes CachedBytes.
Import ListNotations. Local Open Scope Z_scope.

Record layout:=Layout {sp:Z; point_ptr:Z; table_ptr:Z; writable:Z->Prop}.
Definition span a n x:=a<=x<a+n.
Definition stage e:=Frame.staging(sp e).
Definition stack_area e:=Area (sp e-2424) (sp e).
Definition footprint sp pt dst x:=span (sp-2424) 2424 x \/ span pt 1280 x \/ span dst 21760 x.
Definition private e:=footprint (sp e) (point_ptr e) (table_ptr e).
Record placement e : Prop:=Placed {
 stack_fit:fits64 (sp e-2424) 2432;
 stack_alignment:sp e mod 16=8;
 point_fit:fits64 (point_ptr e) 1280;
 point_alignment:point_ptr e mod 64=0;
 table_fit:fits64 (table_ptr e) 21760;
 buffers_disjoint:disjoint (point_ptr e) 1280 (table_ptr e) 21760;
 point_stack:disjoint (point_ptr e) 1280 (sp e-2424) 2432;
 table_stack:disjoint (table_ptr e) 21760 (sp e-2424) 2432;
 permits:forall x,private e x -> writable e x
}.
Lemma depth e : placement e -> sp e-2424<=stage e-1360 /\ stage e+960<=sp e-48 /\ stage e mod 64=0.
Proof.
 intro P;destruct(Frame.frame_geometry (sp e) (stack_alignment _ P)) as [A [D [L H]]].
 unfold stage,Frame.stack_depth in *;rewrite L in D;auto.
Qed.

Definition children:list (Z*list Z):=[(ObjectBytes.address,ObjectBytes.symbol_bytes);
 (DecoderBytes.address,DecoderBytes.symbol_bytes);(HelperBytes.address,HelperBytes.symbol_bytes);
 (CachedBytes.address,CachedBytes.symbol_bytes)].
Record loaded_images images root bias e :Prop:=Loaded {
 symbols:forall a bs,In (a,bs) images -> fits64 (bias+a) (Z.of_nat(length bs)) /\
   available root (writable e) (bias+a) bs
}.
Arguments symbols {images} root bias e _ a bs _.
Definition loaded:=loaded_images children.
Definition origin:=ObjectBytes.address.
Definition text:=ObjectBytes.symbol_bytes.
Definition base bias:=bias+origin.
Definition keep e:=Frame.keep (sp e) (point_ptr e) (table_ptr e).

Lemma builder_in:In(origin,ObjectBytes.symbol_bytes) children. Proof. now left. Qed.
Lemma helper_in:In(HelperBytes.address,HelperBytes.symbol_bytes) children. Proof. now do 2 right;left. Qed.
Lemma decoder_in:In(DecoderBytes.address,DecoderBytes.symbol_bytes) children. Proof. now right;left. Qed.
Lemma cached_in:In(CachedBytes.address,CachedBytes.symbol_bytes) children. Proof. now do 3 right;left. Qed.

Lemma mapped_now root bias e : loaded root bias e -> forall p a bs,
 accounted root (writable e) p -> In (a,bs) children ->
 mapped (mem(machine p)) (bias+a) bs /\ (forall x,bias+a<=x<bias+a+Z.of_nat(length bs)->~writable e x).
Proof.
 intros I p a bs Acc C;destruct(symbols _ _ _ I _ _ C) as [_ [Map Sep]].
 split;[exact (image_after _ _ _ _ _ Acc Map Sep)|exact Sep].
Qed.
Lemma mapped_word root bias e : loaded root bias e -> forall a bs, In(a,bs) children ->
 0<Z.of_nat(length bs) -> word64(bias+a).
Proof. intros I a bs C N;destruct(proj1(symbols _ _ _ I _ _ C));unfold word64;lia. Qed.
Lemma stack_available e : placement e -> VectorProcedure.stack_ok (stack_area e) (writable e).
Proof.
 intros P;destruct(stack_fit _ P);unfold VectorProcedure.stack_ok,stack_area;cbn [bottom ceiling].
 split;[lia|split;[lia|intros x X;apply (permits _ P);left;unfold region in X;cbn [bottom ceiling] in X;unfold span;lia]].
Qed.

Lemma apart a n b m : 0<n -> 0<m -> (forall x,b<=x<b+m -> ~(a<=x<a+n)) -> disjoint a n b m.
Proof.
 intros N M Ex;unfold disjoint. destruct (Z_le_dec (a+n) b);[auto|right].
 destruct (Z_le_dec (b+m) a);[auto|]. exfalso;apply (Ex (Z.max a b));lia.
Qed.
