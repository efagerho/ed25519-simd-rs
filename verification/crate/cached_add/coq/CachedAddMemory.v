From Coq Require Import List ZArith.
From Machine Require Import execution.Blocks memory.MemoryTrace memory.FlatMemory abi.SysV.
From Ed25519Simd.CachedAdd Require Import CachedAddABI.
From Machine Require Export memory.MemoryGeometry.
From Machine Require Import memory.ByteExecution.
From Ed25519Simd Require Export PointFrame.
Import ListNotations. Open Scope Z_scope.
Section Mode.
Variable affine:bool.
Definition mapped pad c := match c with
 | VectorCell a=>vector_ok (abi_layout affine) a false=true
 | ReturnSlot a=>In a(private_slots pad) \/ a=caller_slot pad end.
Definition valid_placement loc size pad := point_placement loc size pad /\
 fits64(origin loc cached)(cache_length affine) /\ origin loc cached mod 64=0 /\
 disjoint(origin loc cached)(cache_length affine)(origin loc point)1280 /\
 disjoint(origin loc cached)(cache_length affine)(origin loc scratch-16)(1312+pad) /\
 disjoint(origin loc cached)(cache_length affine)(code_base loc)size.
Definition flat_frame p size pad es (initial final:state) :=
 forall loc, valid_placement loc size pad ->
 byte_frame p loc (mapped pad) (writable_byte loc pad) (entry_rsp loc pad) es initial final.
Definition memory_safe p size pad (initial final:state) :=
 exists fuel es,record_path fuel p (abi_layout affine)(fst initial)=Some(fst final,es) /\
 writes_only(allowed_write pad)es /\ balanced[(caller_slot pad,Caller)]es /\
 flat_frame p size pad es initial final.
Definition output_initialized p (initial final:state) :=
 exists fuel es,record_path fuel p (abi_layout affine)(fst initial)=Some(fst final,es) /\
 forall loc k,0<=k<1280 ->writes_at loc es(origin loc point+k).
Definition saved_registers := SysV.sysv_saved.
Definition registers_preserved := SysV.preserves_sysv.
Definition stack_restored := SysV.restores_rsp.
End Mode.

Definition cache_contract p affine initial final :=
 (forall off,memory(snd final)(cached,off)=memory(snd initial)(cached,off)) /\
 exists fuel es,record_path fuel p(abi_layout affine)(fst initial)=Some(fst final,es) /\
 forall a,In a(flat_map(read_addresses p)(data_effects es)) ->fst a=cached ->
 0<=snd a /\ snd a+64<=cache_length affine.
