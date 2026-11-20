From Coq Require Import ZArith List Bool.
From Machine Require Import isa.X86.
Import ListNotations. Local Open Scope Z_scope.

(* The two memory addressing forms used here. An optional RAX index uses
   scale one. The constructor separately identifies the LEA with scale two. *)
Record address := Addr { base : nat; indexed : bool; displacement : Z }.
Inductive instruction :=
| LeaTwice (dst index : nat)
| MovZX (two_bytes : bool) (src : address)
| CopyEaxToR11d | ShrR11d (count : nat)
| And32 (dst : nat) (imm : Z) | XorEax (imm : Z) | OrEaxR11d
| ImulEax (imm : Z) | AddRax (src : address)
| LoadY (dst : nat) (src : address) | LoadZ (dst : nat) (src : address)
| InsertY (dst src_reg : nat) (src : address) (upper : bool).

Definition disp8 n := (-128 <=? n) && (n <? 128).
Definition addressing tuple r a :=
  let b := Z.of_nat (base a) in let disp := displacement a in
  let q := disp / tuple in
  let '(mode, ds) :=
    if (disp =? 0) && negb (b mod 8 =? 5) then (0, [])
    else if (disp mod tuple =? 0) && disp8 q then (1, [q mod 256])
         else (2, le32 disp) in
  if indexed a then modrm mode r 4 :: (b mod 8) :: ds
  else modrm mode r b :: (if b mod 8 =? 4 then [0x24] else []) ++ ds.

Definition rex (w:bool) r x b :=
  let v := 0x40 + (if w then 8 else 0) + 4*(r/8) + 2*(x/8) + b/8 in
  if v =? 0x40 then [] else [v].
Definition logic_imm (ext acc_opcode dst imm : Z) :=
  let short := disp8 imm in
  rex false 0 0 dst ++
    (if negb short && (dst =? 0) then acc_opcode :: le32 imm
     else [if short then 0x83 else 0x81; modrm 3 ext dst] ++
          (if short then [imm mod 256] else le32 imm)).
Definition encode ins := match ins with
| LeaTwice d i => let r:=Z.of_nat d in let x:=Z.of_nat i in
    rex true r x r ++ [0x8d;modrm 0 r 4;64+8*(x mod 8)+r mod 8]
| MovZX two a => rex false 0 0 (Z.of_nat (base a)) ++
    [0x0f;if two then 0xb7 else 0xb6] ++ addressing 1 0 a
| CopyEaxToR11d => [0x41;0x89;0xc3]
| ShrR11d n => [0x41;0xc1;0xeb;Z.of_nat n]
| And32 d n => logic_imm 4 0x25 (Z.of_nat d) n
| XorEax n => logic_imm 6 0x35 0 n
| OrEaxR11d => [0x44;0x09;0xd8]
| ImulEax n => if disp8 n then [0x6b;0xc0;n mod 256] else [0x69;0xc0] ++ le32 n
| AddRax a => rex true 0 0 (Z.of_nat (base a)) ++ [0x03] ++ addressing 1 0 a
| LoadY d a => [0xc5; 128*invbit (Z.of_nat d) 3 + 0x7e;0x6f] ++ addressing 1 (Z.of_nat d) a
| LoadZ d a => prefix 1 2 (Z.of_nat d) 0 (Z.of_nat (base a)) ++ [0x6f] ++ addressing 64 (Z.of_nat d) a
| InsertY d r a hi => prefix 3 1 (Z.of_nat d) (Z.of_nat r) (Z.of_nat (base a)) ++ [0x3a] ++
    addressing 32 (Z.of_nat d) a ++ [if hi then 1 else 0]
end.

Definition addr_ok a := (base a <? 16)%nat && (-2^31 <=? displacement a) && (displacement a <? 2^31).
Definition valid ins := match ins with
| LeaTwice d i => (d <? 16)%nat && (i <? 16)%nat && negb (Nat.eqb (d mod 8) 5) && negb (Nat.eqb i 4)
| MovZX _ a | AddRax a => addr_ok a
| LoadY d a => (d <? 16)%nat && (base a <? 8)%nat && addr_ok a
| LoadZ d a => (d <? 32)%nat && addr_ok a
| InsertY d r a _ => (d <? 32)%nat && (r <? 32)%nat && addr_ok a
| ShrR11d n => (0 <? n)%nat && (n <? 32)%nat
| And32 d n => (d <? 16)%nat && (0 <=? n) && (n <? 2^31)
| ImulEax n | XorEax n => (0 <=? n) && (n <? 2^31)
| _ => true end.
