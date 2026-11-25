From Coq Require Import List ZArith Bool.
From Machine Require Import isa.Instructions isa.X86 isa.VectorMoves execution.WordSemantics execution.LinkedCalls.
Import ListNotations. Local Open Scope Z_scope.

Inductive op := Alu (i:instruction) | Or (d a b:nat) | Permute2 (d idx b:nat) |
 AlignedRip (d:nat) (disp:Z) | SubRip (dst src:nat) (disp:Z)
 | MemoryArithmetic (subtract:bool) (dst src base:nat) (disp:Z).
Definition encoding op := match op with
 | Alu i=>Instructions.encode i
 | Or d a b=>rr 1 1 0xeb d a b
 | Permute2 d idx b=>rr 2 1 0x7e d idx b
 | AlignedRip d disp=>prefix 1 1 (Z.of_nat d) 0 5++[0x6f;modrm 0 (Z.of_nat d) 5]++le32 disp
 | SubRip d a disp=>rip_bcst 1 1 0xfb d a disp
 | MemoryArithmetic sub d a b disp=>rm_memory 1 1 (if sub then 0xfb else 0xd4) d a (Z.of_nat b) disp end.
Definition candidate op bs := let bytes:=encoding op in
 if list_eq_dec Z.eq_dec (firstn (length bytes) bs) bytes then Some(length bytes,op) else None.

(* Invert EVEX's register-extension bits, then check the entire encoding.
   Memory forms here have a signed displacement from the end of the instruction. *)
Definition decode (bs:list Z) := match bs with
 | 0x62::p0::p1::p2::opcode::m::rest=>
   let d:=Z.to_nat(m/8 mod 8+8*invbit p0 7+16*invbit p0 4) in
   let a:=Z.to_nat(15-p1/8 mod 16+16*invbit p2 3) in
   let b:=Z.to_nat(m mod 8+8*invbit p0 5+16*invbit p0 6) in
   match opcode with
   | 0x6f=>if m/64=?3 then candidate (Alu(d,Instructions.Copy b)) bs
     else candidate (AlignedRip d (displacement32 (firstn 4 rest))) bs
   | 0x7e=>candidate (Permute2 d a b) bs
   | 0xeb=>candidate (Or d a b) bs
   | 0xdb=>candidate (Alu(d,And a b)) bs
   | 0x73=>let n:=Z.to_nat(hd 0 rest) in
     candidate (Alu(a,if m/8 mod 8=?2 then Shr b n else Shl b n)) bs
   | 0xd4 | 0xfb=>let sub:=opcode=?0xfb in
     if m/64=?3 then candidate (Alu(d,if sub then Sub a b else Add a b)) bs
     else if (sub && (m/64=?0) && (m mod 8=?5))%bool then candidate (SubRip d a (displacement32 (firstn 4 rest))) bs
     else let '(addr,_):=VectorMoves.operands 64 m rest in
       let base:=Z.to_nat(m mod 8+8*invbit p0 5) in
       candidate (MemoryArithmetic sub d a base (IndexedLoad.displacement addr)) bs
   | 0xef=>candidate (Alu(d,Xor a b)) bs
   | 0x40=>candidate (Alu(d,Mul a b)) bs
   | 0xb4 | 0xb5=>candidate (Alu(d,Madd (opcode=?0xb5) a b)) bs
   | _=>None end
 | _=>None end.
