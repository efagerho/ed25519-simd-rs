From Coq Require Import List ZArith.
From Machine Require Import execution.Blocks memory.MemoryTrace memory.FlatMemory abi.SysV.
From Ed25519Simd.Double4 Require Import Double4ABI.
From Machine Require Export memory.MemoryGeometry.
Import ListNotations. Open Scope Z_scope.
Definition caller_slot pad : pointer := (scratch,1288+pad).
Definition saved_slot pad : pointer := (scratch,1280+pad).
Definition private_slots pad := [(scratch,-16);(scratch,-8);saved_slot pad].
Definition allowed_write pad c := match c with
 | VectorCell a=>vector_in point 1280 a \/ vector_in scratch 1280 a
 | ReturnSlot a=>In a(private_slots pad) end.
Definition mapped pad c := match c with
 | VectorCell a=>vector_ok abi_layout a false=true
 | ReturnSlot a=>In a(private_slots pad) \/ a=caller_slot pad end.
Definition entry_rsp loc pad := origin loc scratch+1288+pad.
Definition valid_placement loc size pad :=
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
Definition flat_frame p size pad es (initial final:state) :=
 forall loc,valid_placement loc size pad ->
 (forall x,writes_at loc es x -> writable_byte loc pad x) /\
 forall before,agrees loc(mapped pad)(snd initial)(return_memory(fst initial))before ->
 let after:=replay p loc es(snd initial)before in
 agrees loc(mapped pad)(snd final)(return_memory(fst final))after /\
 (forall x,~writable_byte loc pad x -> after x=before x) /\
 (forall pre tail,es=pre++tail ->
  agrees loc(mapped pad)(effects p(data_effects pre)(snd initial))
   (fold_left update_slots pre(return_memory(fst initial)))(replay p loc pre(snd initial)before) /\
  forall k,0<=k<8 -> replay p loc pre(snd initial)before(entry_rsp loc pad+k)=before(entry_rsp loc pad+k)) /\
 (forall pre a t tail k,es=pre++Pop a t::tail ->0<=k<8 ->
  replay p loc pre(snd initial)before(address_of loc a+k)=word_byte(pc_word loc t)k).
Definition memory_safe p size pad (initial final:state) :=
 exists fuel es,record_path fuel p abi_layout(fst initial)=Some(fst final,es) /\
 writes_only(allowed_write pad)es /\ balanced[(caller_slot pad,Caller)]es /\
 flat_frame p size pad es initial final.
Definition output_initialized p (initial final:state) :=
 exists fuel es,record_path fuel p abi_layout(fst initial)=Some(fst final,es) /\
 forall loc k,0<=k<1280 ->writes_at loc es(origin loc point+k).
Definition saved_registers := SysV.sysv_saved.
Definition registers_preserved := SysV.preserves_sysv.
Definition stack_restored := SysV.restores_rsp.
(* Explicit loads inside a vector fragment are included in the read footprint. *)
Definition read_addresses p e := match e with
 | Read _ a=>[a]
 | Evaluate id bases=>flat_map(fun bd=>
   match find(fun entry=>Nat.eqb(fst entry)(fst bd))bases with
   | Some(_,a)=>[offset a(snd bd)] | None=>[] end)(load_operands(fragment_code p id))
 | _=>[] end.
Definition input_t_unread p(initial final:state) :=
 exists fuel es,record_path fuel p abi_layout(fst initial)=Some(fst final,es) /\
 forall a,In a(flat_map(read_addresses p)(data_effects es)) ->fst a=point ->0<=snd a /\ snd a+64<=960.
