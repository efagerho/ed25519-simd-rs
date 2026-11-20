From Coq Require Import List ZArith.
From Machine Require Import SysV Blocks MemoryTrace FlatMemory.
From Ed25519Simd.Pow2 Require Import Pow2ABI.
From Machine Require Export MemoryGeometry.
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
 (forall x, writes_at loc es x -> writable_byte loc x) /\
 forall before, agrees loc mapped (snd initial) (return_memory (fst initial)) before ->
 let after := replay p loc es (snd initial) before in
 agrees loc mapped (snd final) (return_memory (fst final)) after /\
 (forall x, ~ writable_byte loc x -> after x = before x) /\
 (* At every prefix, both memory views agree with the same byte array,
    and all eight bytes of the incoming caller's return address are intact. *)
 (forall pre tail, es = pre ++ tail ->
   agrees loc mapped (effects p (data_effects pre) (snd initial))
     (fold_left update_slots pre (return_memory (fst initial))) (replay p loc pre (snd initial) before) /\
   forall k, 0 <= k < 8 -> replay p loc pre (snd initial) before (entry_rsp loc+k) =
                            before (entry_rsp loc+k)) /\
 (* The eight concrete stack bytes consumed by every RET encode its actual destination. *)
 (forall pre a t tail k, es = pre ++ Pop a t :: tail -> 0 <= k < 8 ->
   replay p loc pre (snd initial) before (address_of loc a+k) = word_byte (pc_word loc t) k).

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
