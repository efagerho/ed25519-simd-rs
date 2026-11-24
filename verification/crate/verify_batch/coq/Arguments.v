(* Execute the scalar argument setup symbolically. Stack addresses below are
   offsets from the wrapper's RSP at the call site. Qword stack writes are
   aligned and the only byte read precedes the overwrite of that slot. *)
From Coq Require Import List ZArith.
From Machine Require Import isa.IndexedLoad execution.LinkedCalls.
Import ListNotations. Local Open Scope Z_scope.

Inductive operand := Move (dst src:nat) | Lea (dst base:nat) (off:Z)
 | Qword (dst base:nat) (off:Z) | Octet (dst base:nat) (off:Z)
 | Store (src base:nat) (off:Z) | ClearSlot (off:Z) | ClearEax.
Definition memop wide opcode r base off :=
 let reg:=Z.of_nat r in rex wide reg 0 (Z.of_nat base) ++ opcode ++
 addressing 1 reg (Addr base false off).
Definition encode op := match op with
 | Move d s=>LinkedCalls.encoding 0 (Copy d s)
 | Lea d b n=>memop true [0x8d] d b n
 | Qword d b n=>IndexedLoad.encode (LoadG d (Addr b false n))
 | Octet d b n=>memop false [0x0f;0xb6] d b n
 | Store s b n=>memop true [0x89] s b n
 | ClearSlot n=>memop true [0xc7] 0 4 n ++ X86.le32 0
 | ClearEax=>[0x31;0xc0] end.
Definition encoded ops := flat_map encode ops.
Definition setup := [Move 3 7;Move 12 6;Move 13 6;Move 14 2;Move 15 1;Store 8 4 936;Store 9 4 944].
Definition prepare := [Move 7 15;Lea 6 4 512;Qword 2 4 936;Lea 1 4 768].
Definition hash := [Lea 7 4 0;Lea 6 15 256;Move 2 15;Lea 1 4 640;Lea 8 4 704].
Definition score := [Lea 7 4 768;Qword 0 7 64;Store 0 4 856;Octet 2 7 72;
 Qword 0 4 944;Store 0 7 64;Lea 0 15 512;Store 0 7 72;Lea 0 4 0;Store 0 7 80;
 Lea 6 15 2304;Lea 1 4 856;Move 8 14;Move 9 13].
Definition reject := [ClearSlot 856;Lea 7 4 856;Move 6 14;Move 2 13;ClearEax].

Inductive value := Stack (offset:Z) | Scratch (offset:Z) | Incoming (r:nat)
 | MemoryWord (offset:Z) | MemoryByte (offset:Z) | Zero | Unknown.
Definition plus v n := match v with Stack x=>Stack(x+n) | Scratch x=>Scratch(x+n) | _=>Unknown end.
Record view := View { gpr:nat->value; slot:Z->value; writes:list (Z*value) }.
Definition initial := View (fun r=>match r with 4%nat=>Stack 0 | 1%nat=>Scratch 0 | _=>Incoming r end)
 MemoryWord [].
Definition step s op :=
 let r:=gpr s in let m:=slot s in
 let set d v:=View (fun i=>if Nat.eqb i d then v else r i) m (writes s) in
 let save a v:=match a with Stack x=>
   View r (fun i=>if i=?x then v else m i) ((x,v)::writes s)
   | _=>View r m ((-1,Unknown)::writes s) end in
 match op with
 | Move d a=>set d (r a) | Lea d b n=>set d (plus (r b) n)
 | Qword d b n=>set d (match plus (r b) n with Stack a=>m a | _=>Unknown end)
 | Octet d b n=>set d (match plus (r b) n with Stack a=>
      match m a with MemoryWord x=>MemoryByte x | _=>Unknown end | _=>Unknown end)
 | Store a b n=>save (plus (r b) n) (r a) | ClearSlot n=>save (plus (r 4%nat) n) Zero
 | ClearEax=>set 0%nat Zero end.
Definition after_setup := fold_left step setup initial.
(* Only the saved GPRs, frame slots and RSP survive intervening calls. *)
Definition at_call := View (fun r=>if existsb (Nat.eqb r) [3;4;5;12;13;14;15]%nat
 then gpr after_setup r else Unknown) (slot after_setup) [].
Definition arguments ops regs := map (gpr (fold_left step ops at_call)) regs.
Definition stores ops := rev (writes (fold_left step ops at_call)).
Definition call_arguments :=
 map (gpr after_setup) [3;12;13;14;15]%nat=[Incoming 7;Incoming 6;Incoming 6;Incoming 2;Scratch 0] /\
 rev (writes after_setup)=[(936,Incoming 8);(944,Incoming 9)] /\
 arguments prepare [7;6;2;1]%nat=[Scratch 0;Stack 512;Incoming 8;Stack 768] /\
 arguments hash [7;6;2;1;8]%nat=[Stack 0;Scratch 256;Scratch 0;Stack 640;Stack 704] /\
 arguments score [7;6;2;1;8;9]%nat=[Stack 768;Scratch 2304;MemoryByte 840;Stack 856;Incoming 2;Incoming 6] /\
 stores score=[(856,MemoryWord 832);(832,Incoming 9);(840,Scratch 512);(848,Stack 0)] /\
 arguments reject [7;6;2;0]%nat=[Stack 856;Incoming 2;Incoming 6;Zero] /\
 stores reject=[(856,Zero)].
Lemma checked_arguments : call_arguments.
Proof. vm_compute;repeat split;reflexivity. Qed.
