From Coq Require Import ZArith List Bool.
From Machine Require Import isa.X86 isa.Instructions.
From Ed25519Simd.Decode Require Import Kernels Power.
Import ListNotations. Local Open Scope Z_scope.

(* Offsets within each symbol. The cross-symbol call uses the actual ELF VAs. *)
Definition call pc dst := [0xe8] ++ le32 (dst-pc-5).
Definition vectors := flat_map Instructions.encode.
Definition field_rows (store:bool) start base offset :=
 flat_map (fun i=>rm_memory 1 1 (if store then 0x7f else 0x6f) (start+i)%nat 0 base
   (offset+64*Z.of_nat i)) (seq 0 5).
Definition rows store := field_rows store 0.
Definition slot_lea s := match s with
 | Root => [0x4c;0x8d;0x83] ++ le32 960
 | A => [0x4c;0x8d;0x06] | B => [0x4c;0x8d;0x86] ++ le32 320 end.
Definition chain_step pc op := match op with
 | Save Root=>[] | Save A=>rows true 6 0 | Save B=>rows true 6 320
 | Product s=>let a:=slot_lea s in a++call (pc+Z.of_nat(length a)) 0x7b2
 | Squares O=>[] | Squares 1=>call pc 0x59b
 | Squares n=>[0xb9]++le32(Z.of_nat n)++call (pc+5) 0x59b++[0xff;0xc9;0x75;0xf7] end.
Fixpoint chain_bytes pc ops := match ops with []=>[] | op::tail=>
 let b:=chain_step pc op in b++chain_bytes (pc+Z.of_nat(length b)) tail end.
Definition tail_bytes :=
 let load:=rows false 3 960 in load++chain_bytes (0x7f1+Z.of_nat(length load)) chain
 ++rows true 6 0++[0xc3].

Definition at_bytes (image:list Z) (offset:Z) bytes :=
 firstn (length bytes) (skipn (Z.to_nat offset) image)=bytes.
Definition word_bytes n := le32 n ++ le32 (n/2^32).
Definition field_image k decoder_pc decoder helper_pc helper :=
 let ret:=[0xc3] in
 at_bytes helper 0xb90 (vectors(seed_columns k)++call 0xbfc 0xcb0++vectors(fold_columns k)++ret) /\
 length(vectors(seed_columns k))=0x6c%nat /\
 at_bytes helper 0xcb0 (vectors(convolve k)++ret) /\
 at_bytes decoder 0x59b (vectors(square k)++ret) /\
 at_bytes decoder 0x7b2 (call 0x7b2 0xa57++vectors(tighten k)++ret) /\
 at_bytes decoder 0xa57 (field_rows false 5 8 0 ++ call (decoder_pc+0xa79) (helper_pc+0xb90)
   ++vectors(carry k)++ret) /\
 at_bytes helper 0xde0 (flat_map word_bytes [19;2^51-1;(2^51-19)*1024;(2^51-1)*1024]).

Definition kernel_image k decoder_pc decoder helper_pc helper :=
 field_image k decoder_pc decoder helper_pc helper /\ at_bytes decoder 0x7f1 tail_bytes.
