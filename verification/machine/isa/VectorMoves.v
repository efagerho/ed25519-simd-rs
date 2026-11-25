(* Decode unmasked VEX/EVEX moves and permutations used by
   descriptor and point-table transposes. Accept a candidate only if its existing ISA
   encoder reproduces every consumed byte, including SIB and displacement. *)
From Coq Require Import List ZArith Bool.
From Machine Require Import isa.IndexedLoad isa.Move.
From Machine Require execution.LinkedCalls.
Import ListNotations. Local Open Scope Z_scope.

Inductive operation :=
| Input (i:IndexedLoad.instruction)
| Output (src base:nat) (disp:Z)
| Extract (src base:nat) (disp:Z) (high:bool)
| LowWord (src base:nat) (disp:Z).

Definition encoding op := match op with
 | Input i=>IndexedLoad.encode i
 | Output src base disp=>Move.encode_store src (Z.of_nat base) disp
 | Extract src base disp hi=>X86.prefix 3 1 (Z.of_nat src) 0 (Z.of_nat base)++[0x3b]++
     IndexedLoad.addressing 32 (Z.of_nat src) (Addr base false disp)++[if hi then 1 else 0]
 | LowWord src base disp=>
   let r:=Z.of_nat src in let b:=Z.of_nat base in
   (if (base<?8)%nat then [0xc5;128*X86.invbit r 3+0x79]
    else [0xc4;128*X86.invbit r 3+0x41;0x79]) ++ [0xd6] ++
   IndexedLoad.addressing 1 r (Addr base false disp) end.

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
 | 0xc5::p::0xd6::m::rest=>
   let '(a,_) := operands 1 m rest in
   candidate (LowWord (Z.to_nat (m/8 mod 8+8*X86.invbit p 7)) (base a) (displacement a)) bs
 | 0xc4::p::0x79::0xd6::m::rest=>
   let '(a,_) := operands 1 m rest in
   candidate (LowWord (Z.to_nat (m/8 mod 8+8*X86.invbit p 7))
     (Z.to_nat (m mod 8+8*X86.invbit p 5)) (displacement a)) bs
 | 0xc5::0xfe::0x6f::m::rest=>
   let '(a,_) := operands 1 m rest in
   candidate (Input (LoadY (Z.to_nat (m/8 mod 8)) a)) bs
 | 0x62::p0::p1::p2::opcode::m::rest=>
   let dst:=Z.to_nat (m/8 mod 8+8*X86.invbit p0 7+16*X86.invbit p0 4) in
   let src:=Z.to_nat (15-p1/8 mod 16+16*X86.invbit p2 3) in
   let base:=Z.to_nat (m mod 8+8*X86.invbit p0 5) in
   let rm:=Z.to_nat (m mod 8+8*X86.invbit p0 5+16*X86.invbit p0 6) in
   match opcode with
   | 0x6f=>let '(a,_):=operands 64 m rest in candidate (Input (LoadZ dst (Addr base false (displacement a)))) bs
   | 0x3a=>let '(a,imm):=operands 32 m rest in
           candidate (Input (InsertY dst src (Addr base false (displacement a)) (hd 0 imm=?1))) bs
   | 0x3b=>let '(a,imm):=operands 32 m rest in candidate (Extract dst base (displacement a) (hd 0 imm=?1)) bs
   | 0x6c | 0x6d=>candidate (Input (UnpackWords (opcode=?0x6d) dst src rm)) bs
   | 0x43=>candidate (Input (ShuffleWords dst src rm (Z.to_nat (hd 0 rest)))) bs
   | 0x7f=>let '(a,_):=operands 64 m rest in candidate (Output dst base (displacement a)) bs
   | _=>None end
 | _=>None end.

(* Aligned 512-bit VMOVDQA64 with a GPR base, including R8--R15.
   Re-encoding rejects masked, indexed, RIP-relative and register forms. *)
Record aligned_row := Row { writing:bool; zmm:nat; gpr:nat; offset:Z }.
Definition row_encoding i := X86.rm_memory 1 1 (if writing i then 0x7f else 0x6f)
 (zmm i) 0 (Z.of_nat (gpr i)) (offset i).
Definition decode_row (bs:list Z) := match bs with
 | 0x62::p0::0xfd::0x48::opcode::m::rest=>
   let '(a,_):=operands 64 m rest in
   let r:=Z.to_nat (m/8 mod 8+8*X86.invbit p0 7+16*X86.invbit p0 4) in
   let b:=Z.to_nat (m mod 8+8*X86.invbit p0 5) in
   let i:=Row (opcode=?0x7f) r b (displacement a) in
   let enc:=row_encoding i in
   if list_eq_dec Z.eq_dec (firstn (length enc) bs) enc then Some(length enc,i) else None
 | _=>None end.
