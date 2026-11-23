From Coq Require Import List ZArith Bool.
From Machine Require Import execution.WordSemantics memory.ByteMemory.
From Ed25519Simd.Sha512Challenge Require Import Image.
Import ListNotations.
Local Open Scope Z_scope.

Definition pos l := Z.of_nat (offset l listing).
Definition s32 code at_pc :=
 signed_value (2^31) (read_le 4 (fun i=>nth (Z.to_nat i) code 0) at_pc).
Definition relative code next := next + s32 code (next-4).
(* Check control transfers against their role in the execution, independently
   of the opcode supplied to the image encoder. Empty is reached on borrow,
   Full on unsigned >=, Next/Return on a zero mask and Tails on a set bit. *)
Definition transfer code at_pc target :=
 let byte k := nth (Z.to_nat (at_pc+k)) code 0 in
 let short opcode := (byte 0 =? opcode) &&
   (at_pc+2+signed_value 128 (byte 1) =? pos target) in
 let near opcode := (byte 0 =? opcode) && (relative code (at_pc+5) =? pos target) in
 match target with
 | Rows => near 0xe8 | Block => near 0xe9
 | Expanded => (byte 0 =? 0x0f) && (byte 1 =? 0x85) && (relative code (at_pc+6) =? pos target)
 | Next | Return => short 0x74 | Tails => short 0x75
 | Empty _ => short 0x72 | Full _ => short 0x73 | Loaded _ => short 0xeb
 | _ => false end.
Fixpoint edges code at_pc items := match items with
 | []=>true | x::xs=>(match x with Branch _ _ target => transfer code at_pc target | _=>true end)
                    && edges code (at_pc+Z.of_nat (width x)) xs end.

(* Follow ADD R10,imm32; CMP R10,RDX; JNE rel32. Each visited body uses
   sixteen consecutive K broadcasts. Fuel exhaustion is a certification failure. *)
Fixpoint key_groups fuel cursor limit stride := match fuel with
| O => None
| S n => let next:=cursor+stride in
  if next =? limit then Some [cursor;next] else
  option_map (cons cursor) (key_groups n next limit stride) end.

Record plan := Plan { keys:list Z; depth:Z; row_step:nat; upper:Z; lower:Z }.
Definition decode pc code :=
 let top:=pos AfterUpper in let bottom:=pos AfterLower in
 let advance l := signed_value 128 (nth (Z.to_nat (pos l+3)) code 0) in
 if (advance FullAdvance =? advance TailAdvance) && (0 <=? advance FullAdvance) &&
    edges code 0 listing then
 let start:=pc+relative code (pos KeyLimit) in let limit:=pc+relative code (pos Expanded) in
 option_map (fun groups=>Plan groups (s32 code (pos FrameSize+3))
                         (Z.to_nat (advance FullAdvance)) (pc+top) (pc+bottom))
   (key_groups 4 start limit (s32 code (pos KeyIncrement+3)))
 else None.
(* Independently decode every other RIP-relative load used by a specialized
   group. This permits the group interpreter to use the checked shuffle mask,
   prefix size, final-block bias and contiguous IV layout. *)
Definition loads_match pc ro code :=
 let refers l k := pc+relative code (pos l) =? ro+k in
 refers PrefixLength 64 && refers LastBias 72 &&
 forallb (fun i=>refers (IV i) (128+8*Z.of_nat i)) (seq 0 8) &&
 refers (SwapMask 0) 0 && refers (SwapMask 8) 0 && refers PublishMask 0.

Definition expected pc ro :=
 Plan (map (fun n=>ro+192+128*Z.of_nat n) (seq 0 5)) 704 64 (pc+pos AfterUpper) (pc+pos AfterLower).
