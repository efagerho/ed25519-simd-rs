From Machine Require Import memory.ByteExecution.
From Coq Require Import List ZArith.
From Machine Require Import abi.SysV execution.Blocks memory.MemoryTrace memory.FlatMemory.
From Ed25519Simd.Pow2 Require Import Pow2ABI.
From Machine Require Export memory.MemoryGeometry.
Import ListNotations.
Open Scope Z_scope.

Definition caller_slot : pointer := (stack,1928).
Definition private_slot : pointer := (stack,-8).
Definition allowed_write s := match s with
 | VectorCell a => vector_in output 640 a \/ vector_in stack 1920 a
 | ReturnSlot a => a = private_slot
 end.
Definition mapped s := match s with
 | VectorCell a => vector_ok abi_layout a false = true
 | ReturnSlot a => a = private_slot \/ a = caller_slot
 end.

Definition entry_rsp loc := origin loc stack + 1928.

(* Region bases need no vector alignment. The two read-only inputs may alias.
   The stack interval includes the private slot, scratch, gap and caller slot. *)
Definition valid_placement loc code_size :=
 let a := origin loc input_a in let b := origin loc input_b in
 let o := origin loc output in let s := entry_rsp loc - 1936 in
 fits64 a 320 /\ fits64 b 320 /\ fits64 o 640 /\ fits64 s 1944 /\
 entry_rsp loc mod 16 = 8 /\ fits64 (code_base loc) code_size /\
 0 <= caller_pc loc < 2^64 /\ ~(code_base loc <= caller_pc loc < code_base loc + code_size) /\
 disjoint o 640 s 1944 /\ disjoint o 640 a 320 /\ disjoint o 640 b 320 /\
 disjoint s 1944 a 320 /\ disjoint s 1944 b 320 /\
 disjoint o 640 (code_base loc) code_size /\ disjoint s 1944 (code_base loc) code_size.

(* Half-open byte ranges. The eight bytes just below entry RSP are padding. *)
Definition writable_byte loc x :=
 origin loc output <= x < origin loc output+640 \/
 entry_rsp loc-1936 <= x < entry_rsp loc-8.

Definition flat_frame p code_size es (initial final : state) :=
 forall loc, valid_placement loc code_size ->
 byte_frame p loc mapped (writable_byte loc) (entry_rsp loc) es initial final.

Definition memory_safe p code_size (initial final : state) :=
 exists fuel es,
   record_path fuel p abi_layout (fst initial) = Some (fst final,es) /\
   writes_only allowed_write es /\ balanced [(caller_slot,Caller)] es /\
   flat_frame p code_size es initial final.

(* Every byte of the 640-byte output at the entry RDI pointer is actually
   written along the returning execution. This has no arithmetic precondition
   and does not depend on the previous contents of the output storage. *)
Definition output_initialized p (initial final : state) :=
 exists out fuel es,
   Blocks.gpr (fst initial) 7%nat = Ptr out /\
   record_path fuel p abi_layout (fst initial) = Some (fst final,es) /\
   forall loc k, 0 <= k < 640 -> writes_at loc es (address_of loc out+k).

(* SysV AMD64 nonvolatile integer registers: RBX, RBP and R12 through R15.
   RSP has its own postcondition because RET consumes an eight-byte address. *)
Definition saved_registers := SysV.sysv_saved.
Definition registers_preserved := SysV.preserves_sysv.
