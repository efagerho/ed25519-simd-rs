From Coq Require Import ZArith List Bool Lia.
From Machine Require Import execution.Blocks execution.ExecutionProperties memory.MemoryTrace memory.FlatMemory
 memory.MemoryGeometry memory.MemoryCoverage memory.Alignment abi.SysV.
Import ListNotations. Local Open Scope Z_scope.

Definition scratch := 0%nat.
Definition point := 1%nat.
Definition point_layout (extra : layout) : layout := fun r cell =>
 if Nat.eqb r scratch then
   if (0 <=? cell) && (cell <? 20) then WriteVector
   else if cell =? -1 then ReturnWords 192
   else if cell =? 20 then ReturnWords 255 else Unmapped
 else if Nat.eqb r point && (0 <=? cell) && (cell <? 20) then WriteVector else extra r cell.
Definition permitted_padding pad := In pad [0;16;32;48].
Definition caller_slot pad : pointer := (scratch,1288+pad).
Definition saved_slot pad : pointer := (scratch,1280+pad).
Definition private_slots pad := [(scratch,-16);(scratch,-8);saved_slot pad].
Definition allowed_write pad c := match c with
 | VectorCell a=>vector_in point 1280 a \/ vector_in scratch 1280 a
 | ReturnSlot a=>In a(private_slots pad) end.
Definition entry_rsp loc pad := origin loc scratch+1288+pad.
Definition point_placement loc size pad :=
 permitted_padding pad /\
 fits64 (origin loc point) 1280 /\ origin loc point mod 64=0 /\
 fits64 (origin loc scratch-16)(1312+pad) /\ origin loc scratch mod 64=0 /\
 fits64 (code_base loc) size /\ 0<=caller_pc loc<2^64 /\
 ~(code_base loc<=caller_pc loc<code_base loc+size) /\
 disjoint (origin loc point)1280 (origin loc scratch-16)(1312+pad) /\
 disjoint (origin loc point)1280 (code_base loc)size /\
 disjoint (origin loc scratch-16)(1312+pad)(code_base loc)size.
(* The interval includes the RBP save and alignment padding, and both nested
   return slots. With the permitted padding its size is at most 1352 bytes. *)
Definition writable_byte loc pad x :=
 origin loc point<=x<origin loc point+1280 \/
 origin loc scratch-16<=x<entry_rsp loc pad.
Lemma padding_range pad : permitted_padding pad -> 0<=pad<=48.
Proof. intros[<- | [<- | [<- | [<- | []]]]];lia. Qed.
Lemma permitted_bytes loc pad es x : permitted_padding pad -> writes_only(allowed_write pad)es ->
 writes_at loc es x -> writable_byte loc pad x.
Proof.
 intros Pad W[e[s[I[E K]]]];pose proof(padding_range _ Pad)as PB.
 apply Forall_forall with(x:=e)in W;[|exact I];rewrite E in W;destruct s as[[r d]|a].
 - destruct W as[A|A];unfold vector_in in A;cbn [fst snd] in A;destruct A as[-> [L[U _]]];
   unfold inside,cell_address,address_of in K;cbn [width fst snd] in K;unfold writable_byte,entry_rsp;lia.
 - cbn [allowed_write private_slots] in W;destruct W as[<- | [<- | [<- | []]]];
   unfold inside,cell_address,address_of,saved_slot in K;cbn [width fst snd] in K;unfold writable_byte,entry_rsp;lia.
Qed.
Definition write_ok pad e := match destination e with
 | Some(VectorCell a)=>cell_inb point 1280 a || cell_inb scratch 1280 a
 | Some(ReturnSlot a)=>existsb(ptr_eq a)(private_slots pad) | None=>true end.
Lemma write_ok_sound pad es : forallb(write_ok pad)es=true -> writes_only(allowed_write pad)es.
Proof.
 rewrite forallb_forall;unfold writes_only;rewrite Forall_forall;intros H e I;specialize(H e I).
 unfold write_ok in H;destruct(destination e)as[[a|a]|];cbn [allowed_write];[| |exact Logic.I].
 - rewrite orb_true_iff,!cell_inb_spec in H;exact H.
 - apply existsb_exists in H as[b[B E]];apply ptr_eq_true in E;now subst.
Qed.
Lemma caller_byte_protected loc size pad k : point_placement loc size pad ->0<=k<8 ->
 ~writable_byte loc pad(entry_rsp loc pad+k).
Proof. intros[Pad[_[_[_[_[_[_[_[OS _]]]]]]]]]K;pose proof(padding_range _ Pad);unfold disjoint in OS;unfold writable_byte,entry_rsp in *;lia. Qed.
Lemma stack_limit loc pad x : permitted_padding pad -> origin loc scratch-16<=x<entry_rsp loc pad ->
 entry_rsp loc pad-1352<=x<entry_rsp loc pad.
Proof. intros P R;pose proof(padding_range _ P);unfold entry_rsp in *;lia. Qed.
Lemma placement_alignment loc size pad : point_placement loc size pad ->
 Z.land(entry_rsp loc pad-8)(-64)-1280=origin loc scratch.
Proof.
 intros[Pad[_[_[_[Aligned _]]]]].
 unfold entry_rsp;replace(origin loc scratch+1288+pad-8)with(origin loc scratch+(1280+pad))by ring.
 rewrite aligned_region_and by exact Aligned.
 destruct Pad as[<- | [<- | [<- | [<- | []]]]];change(origin loc scratch+1280-1280=origin loc scratch);ring.
Qed.
