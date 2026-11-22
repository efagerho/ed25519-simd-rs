From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.X86 isa.Instructions isa.Arithmetic.
From Machine Require execution.Packed.
From Ed25519Simd.Decode Require Import Glue.
From Ed25519Simd.KeyTable Require Import Fields.
Import ListNotations. Local Open Scope nat_scope.

Inductive op :=
 | Unpack (high:bool) (dst a b:nat) | Shuffle (dst a b imm:nat)
 | Copy (dst a:nat) | Permute (dst indices b:nat) | MaskSub (dst a b:nat)
 | Store (positive:bool) (offset src:nat)
 | Extract (positive:bool) (offset src half:nat).

Definition join a b c d imm lo hi :=
 [Shuffle 28 a b imm; Shuffle 29 c d imm; Shuffle lo 28 29 136; Shuffle hi 28 29 221].
Definition eight (single:bool) a b c d e f g h :=
 [Unpack false 10 a b; Unpack false 12 c d; Unpack false 14 e f; Unpack false 26 g h] ++
 if single then [Shuffle 28 10 12 136; Shuffle 29 14 26 136; Shuffle a 28 29 136]
 else [Unpack true 11 a b; Unpack true 13 c d; Unpack true 15 e f; Unpack true 27 g h] ++
 join 10 12 14 26 136 a e ++ join 10 12 14 26 221 c g ++
 join 11 13 15 27 136 b f ++ join 11 13 15 27 221 d h.
Definition transpose single :=
 eight single 16 17 18 19 20 21 22 23 ++ eight single 24 25 5 6 7 8 9 0.
Definition four high := [Unpack high 10 1 2; Unpack high 11 3 4;
 Shuffle 12 10 11 68; Shuffle 13 10 11 238; Shuffle 10 12 13 136; Shuffle 11 12 13 221].
Definition row lane a b tail half :=
 let o:=340*lane in [Store true o a;Store true (o+8) b;Copy 12 a;
 Permute 12 28 b;Permute a 29 b;MaskSub a 30 a;Store false o 12;Store false (o+8) a;
 Extract true (o+16) tail half;Extract false (o+16) tail half].
Definition first := four false ++ row 0 16 24 10 0.
Definition rest := row 4 20 7 10 1 ++ row 2 18 5 11 0 ++ row 6 22 9 11 1 ++
 four true ++ row 1 17 25 10 0 ++ row 5 21 8 10 1 ++ row 3 19 6 11 0 ++ row 7 23 0 11 1.
Definition index0 := [5;6;7;8;9;0;1;2]%Z.
Definition index8 := [3;4;10;11;12;13;14;15]%Z.
Definition biases := [0;0;2^52-38;2^52-2;2^52-2;2^52-2;2^52-2;0]%Z.
Definition mask := 124%Z.

(* Extract writes a 32-byte tuple. Its compressed displacement scales by 32. *)
Definition store_base (p:bool) := if p then 13%Z else 14%Z.
Definition extract_bytes p o r half :=
 let b:=store_base p in let disp:=(8*Z.of_nat o)%Z in let scaled:=(disp/32)%Z in
 let short:=((disp mod 32 =? 0) && (scaled <? 128))%Z%bool in
 X86.prefix 3 1 (Z.of_nat r) 0 b ++ [0x3b%Z;modrm (if short then 1 else 2) (Z.of_nat r) b] ++
 (if short then [scaled] else le32 disp) ++ [Z.of_nat half].
Definition bytes op := match op with
 | Unpack high d a b=>Packed.encode (Packed.UnpackQ high d a b)
 | Shuffle d a b imm=>Packed.encode (Packed.Shuffle d a b imm)
 | Copy d a=>Instructions.encode (d,Instructions.Copy a)
 | Permute d i b=>rr 2 1 0x7e d i b
 | MaskSub d a b=>mask_bytes 1 (rr 1 1 0xfb d a b)
 | Store p o r=>rm_memory 1 2 0x7f r 0 (store_base p) (8*Z.of_nat o)
 | Extract p o r h=>extract_bytes p o r h end.

(* Symbolically execute the lane instructions. Scratch words have no table
   interpretation. A stray read leaves an Unknown in the store trace. *)
Inductive word := Input (column lane:nat) | Literal (z:Z) | Subtract (bias:Z) (w:word) | Unknown.
(* Product may write all temporaries. Each later carry only writes the
   output and registers 10..14. Keep the five field digits exactly where the
   caller copies them after returning from each helper. *)
Definition after_field (before:nat->nat->word) op r j :=
 let at_field start := (start<=?r) && (r<?start+5) in
 if at_field (saved_in op) then Input (column_start op+(r-saved_in op)) j
 else if at_field 0 then Input (column_start op+r) j
 else if match op with TwoDT=>true | _=>(10<=?r) && (r<?15) end then Unknown
 else before r j.
Definition initial := fold_left after_field field_order (fun _ _=>Unknown).
Definition constant v j := Literal (nth j v 0%Z).
Definition event := (bool * nat * list word)%type.
Definition state := ((nat->nat->word) * list event)%type.
(* Use the machine library's byte-level unpack and shuffle. Collapse an
   output qword to a source word only if all eight byte positions agree. *)
Definition packed_lane (r:nat->nat->word) op dst j :=
 let v:=Packed.zmm (Packed.step Packed.initial op) dst in
 let octet k:=Packed.byte v (8*j+k) in match octet 0 with
 | Packed.Octet (Packed.Initial src lane) O=>
   if forallb (fun k=>match octet k with Packed.Octet (Packed.Initial s l) n=>
     Nat.eqb s src && Nat.eqb l lane && Nat.eqb n k | _=>false end) (seq 0 8)
   then r src lane else Unknown
 | _=>Unknown end.
Definition step (s:state) cmd : state :=
 let '(r,writes):=s in let set dst v:=(put r dst v,writes) in
 let emit p o src start len := (r,writes++[(p,o,map (r src) (seq start len))]) in
 match cmd with
 | Unpack hi d a b=>set d (packed_lane r (Packed.UnpackQ hi d a b) d)
 | Shuffle d a b imm=>set d (packed_lane r (Packed.Shuffle d a b imm) d)
 | Copy d a=>set d (r a)
 | Permute d i b=>set d (fun j=>match r i j with Literal n=>
   let k:=Z.to_nat (n mod 16) in r (if k <? 8 then d else b) (k mod 8) | _=>Unknown end)
 | MaskSub d a b=>set d (fun j=>if Z.testbit mask (Z.of_nat j)
   then match r a j with Literal z=>Subtract z (r b j) | _=>Unknown end else r d j)
 | Store p o src=>emit p o src 0 8 | Extract p o src half=>emit p o src (4*half) 4 end.
Definition signed_word (positive:bool) i j :=
 if positive then Input i j else if i <? 5 then Input (5+i) j
 else if i <? 10 then Input (i-5) j else if i <? 15 then
 Subtract (if Nat.eqb i 10 then (2^52-38)%Z else (2^52-2)%Z) (Input i j) else Input i j.
