From Coq Require Import List ZArith.
From Machine Require Import isa.Instructions execution.MaskTrace execution.MaskStores memory.WriteTrace memory.ByteMemory.
Import ListNotations. Local Open Scope Z_scope.

(* A call after a vector spill must push its own relocated continuation.
   The helper clears EAX and returns. The outer frame then restores RBP. *)
Local Definition code:=map Op [PushBP;SetBP;SubSP 64;Vector (2%nat,Add 0 1);
 MaskTrace.Store 2 4 0;Call 5;RestoreSP;PopBP;Return;ZeroEax;Return].
Local Definition t:=program_writes 11 80 0 code 3.
Local Definition input (_ _:nat) (_:nat):=0.
Local Definition lane_register (j r:nat):=256*Z.of_nat j+Z.of_nat r.
Local Definition ws:=events 65536 4216 3 0x1234 t input lane_register.
Example saved_vector_and_call_data :
 result t input lane_register=Some 0 /\ map address ws=[4208;4144;4136] /\
 map size ws=[8;64;8]%nat /\
 let m:=replay (fun _=>0) ws in read_word m 4208=0x1234 /\
 read_word m 4144=1 /\ read_word m 4200=3585 /\
 match ws with [_;_;last]=> read_word m 4136=pc last+5 | _=>False end.
Proof. vm_compute;repeat split;reflexivity. Qed.

From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MaskReturn memory.FlatMemory.
Local Definition cpu0:=CPU (fun r=>if Nat.eqb r 4 then 4216 else 0x1234) lane_register
 (Some false) (write_bytes (fun _=>0) 4216 8 (word_byte 0xabcdef)).
Local Definition entry:=Cursor 65536 cpu0 (Some true) [].
Example returned_registers_and_flags :
 match execute 65536 3 t input entry (fun _ _=>true) with
 |Some(q,ks)=>ip q=0xabcdef /\ LinkedCalls.regs(machine q) 4%nat=4224 /\
   LinkedCalls.regs(machine q) 5%nat=0x1234 /\ vectors(machine q) 7%nat 2%nat=3585 /\
   flag(machine q)=Some true /\ carry q=Some false /\ ks 1%nat 40%nat=true
 |None=>False end.
Proof. vm_compute;repeat split;reflexivity. Qed.

(* Testing an all-eight-lane predicate sets neither ZF nor CF. KORTESTW
   also inspects the eight zero high bits of this qword comparison. *)
Local Definition masks:=program_writes 5 0 0 (map Op
 [CompareQ 1 0 0;TestMask 1;KmovEax 1;VZeroUpper;MaskTrace.Return]) 3.
Example all_lanes_kortestw :
 match execute 65536 3 masks input entry (fun _ _=>true) with
 |Some(q,ks)=>LinkedCalls.regs(machine q) 0%nat=255 /\ flag(machine q)=Some false /\ carry q=Some false /\
   ks 1%nat 7%nat=true /\ ks 1%nat 8%nat=false /\ vectors(machine q) 6%nat 15%nat=0 /\
   vectors(machine q) 6%nat 16%nat=1552
 |None=>False end.
Proof. vm_compute;repeat split;reflexivity. Qed.
