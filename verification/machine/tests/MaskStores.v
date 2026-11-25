From Coq Require Import List ZArith.
From Machine Require Import isa.Instructions execution.MaskTrace execution.MaskStores memory.WriteTrace memory.ByteMemory.
Import ListNotations. Local Open Scope Z_scope.

(* A call after a vector spill must push its own relocated continuation.
   The helper clears EAX and returns. The outer frame then restores RBP. *)
Local Definition code:=map Op [PushBP;SetBP;SubSP 64;Vector (2%nat,Add 0 1);
 MaskTrace.Store 2 4 0;Call 5;RestoreSP;PopBP;Return;ZeroEax;Return].
Local Definition t:=program_writes 11 80 0 code 3.
Local Definition input (_ _:nat) (_:nat):=0.
Local Definition initial (j r:nat):=256*Z.of_nat j+Z.of_nat r.
Local Definition ws:=events 65536 4216 3 0x1234 t input initial.
Example saved_vector_and_call_data :
 result t input initial=Some 0 /\ map address ws=[4208;4144;4136] /\
 map size ws=[8;64;8]%nat /\
 let m:=replay (fun _=>0) ws in read_word m 4208=0x1234 /\
 read_word m 4144=1 /\ read_word m 4200=3585 /\
 match ws with [_;_;last]=> read_word m 4136=pc last+5 | _=>False end.
Proof. vm_compute;repeat split;reflexivity. Qed.
