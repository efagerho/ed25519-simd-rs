From Coq Require Import List ZArith.
From Machine Require Import Blocks MemoryTrace FlatMemory.
Require Import ScalarABI.
Import ListNotations. Open Scope Z_scope.
Definition caller_slot : pointer := (stack,0).
Definition vector_in region length(a:pointer) :=
 fst a=region /\0<=snd a /\snd a+64<=length /\snd a mod 64=0.
Definition allowed_write c := match c with VectorCell a=>vector_in output 320 a | ReturnSlot _=>False end.
Definition mapped c := match c with VectorCell a=>vector_in output 320 a \/vector_in input 512 a
 | ReturnSlot a=>a=caller_slot end.
Definition fits64 base len := 0<=base /\base+len<=2^64.
Definition valid_placement loc size :=
 fits64(origin loc output)320 /\ fits64(origin loc input)512 /\
 fits64(origin loc stack)8 /\origin loc stack mod 16=8 /\
 fits64(code_base loc)size /\0<=caller_pc loc<2^64 /\
 ~(code_base loc<=caller_pc loc<code_base loc+size) /\
 disjoint(origin loc output)320(origin loc input)512 /\
 disjoint(origin loc output)320(origin loc stack)8 /\
 disjoint(origin loc output)320(code_base loc)size /\
 disjoint(origin loc input)512(origin loc stack)8 /\
 disjoint(origin loc input)512(code_base loc)size /\
 disjoint(origin loc stack)8(code_base loc)size.
Definition writable_byte loc x := origin loc output<=x<origin loc output+320.
Definition flat_frame p size es(initial final:state) :=
 forall loc,valid_placement loc size ->
 (forall x,writes_at loc es x ->writable_byte loc x) /\
 forall before,agrees loc mapped(snd initial)(return_memory(fst initial))before ->
 let after:=replay p loc es(snd initial)before in
 agrees loc mapped(snd final)(return_memory(fst final))after /\
 (forall x,~writable_byte loc x ->after x=before x) /\
 (forall pre tail,es=pre++tail ->
 agrees loc mapped(effects p(data_effects pre)(snd initial))
 (fold_left update_slots pre(return_memory(fst initial)))(replay p loc pre(snd initial)before) /\
 forall k,0<=k<8 ->replay p loc pre(snd initial)before(origin loc stack+k)=before(origin loc stack+k)) /\
 (forall pre a t tail k,es=pre++Pop a t::tail ->0<=k<8 ->
 replay p loc pre(snd initial)before(address_of loc a+k)=word_byte(pc_word loc t)k).
Definition memory_safe p size(initial final:state) :=
 exists fuel es,record_path fuel p abi_layout(fst initial)=Some(fst final,es) /\
 writes_only allowed_write es /\balanced[(caller_slot,Caller)]es /\flat_frame p size es initial final.
Definition output_initialized p(initial final:state) :=
 exists fuel es,record_path fuel p abi_layout(fst initial)=Some(fst final,es) /\
 forall loc k,0<=k<320 ->writes_at loc es(origin loc output+k).
