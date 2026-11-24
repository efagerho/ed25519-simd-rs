(* Decode the low-register, unmasked VEX/EVEX moves and permutations used by
   the descriptor transpose. Accept a candidate only if its existing ISA
   encoder reproduces every consumed byte, including SIB and displacement. *)
From Coq Require Import List ZArith Bool.
From Machine Require Import isa.IndexedLoad isa.Move.
From Machine Require execution.LinkedCalls.
Import ListNotations. Local Open Scope Z_scope.

Inductive operation :=
| Input (i:IndexedLoad.instruction)
| Output (src base:nat) (disp:Z).

Definition encoding op := match op with
 | Input i=>IndexedLoad.encode i
 | Output src base disp=>Move.encode_store src (Z.of_nat base) disp end.

Definition candidate op bs :=
 let bytes:=encoding op in
 if list_eq_dec Z.eq_dec (firstn (length bytes) bs) bytes
 then Some (length bytes,op) else None.

Definition operands tuple m (tail:list Z) :=
 let base:=m mod 8 in
 let ds:=if base=?4 then tl tail else tail in
 let after_disp:=match m/64 with 1=>tl ds | 2=>skipn 4 ds | _=>ds end in
 let disp:=match m/64 with
 | 1=>WordSemantics.signed_value 128 (hd 0 ds)*tuple
 | 2=>LinkedCalls.displacement32 (firstn 4 ds)
 | _=>0 end in
 (Addr (Z.to_nat base) false disp,after_disp).

Definition decode (bs:list Z) : option (nat*operation) :=
 match bs with
 | 0xc5::0xfe::0x6f::m::rest=>
   let '(a,_) := operands 1 m rest in
   candidate (Input (LoadY (Z.to_nat (m/8 mod 8)) a)) bs
 | 0x62::_::p1::0x48::opcode::m::rest=>
   let dst:=Z.to_nat (m/8 mod 8) in let src:=Z.to_nat (15-p1/8 mod 16) in
   let rm:=Z.to_nat (m mod 8) in
   match opcode with
   | 0x6f=>let '(a,_):=operands 64 m rest in candidate (Input (LoadZ dst a)) bs
   | 0x3a=>let '(a,imm):=operands 32 m rest in
           candidate (Input (InsertY dst src a (hd 0 imm=?1))) bs
   | 0x6c | 0x6d=>candidate (Input (UnpackWords (opcode=?0x6d) dst src rm)) bs
   | 0x43=>candidate (Input (ShuffleWords dst src rm (Z.to_nat (hd 0 rest)))) bs
   | 0x7f=>let '(a,_):=operands 64 m rest in candidate (Output dst (base a) (displacement a)) bs
   | _=>None end
 | _=>None end.
