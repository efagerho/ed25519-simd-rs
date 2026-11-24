From Coq Require Import List Bool ZArith Lia.
From Machine Require Import isa.X86 isa.Shift isa.ProgramLayout execution.Packed.
From SHA512 Require Import Spec.
From Ed25519Simd.Sha512Challenge Require Import Rounds Transpose Block.
Import ListNotations.
Local Open Scope Z_scope.

Definition le64 (n:N) := map (fun i => (Z.of_N n / 2^(8*Z.of_nat i)) mod 256) (seq 0 8).
Definition literals :=
  map (fun i=>Z.of_nat (swap i)) (seq 0 64) ++ le64 64 ++ le64 80 ++ repeat 0 48 ++
  flat_map le64 (spill Spec.initial ++ constants).

Inductive label := Block | Rows | Expanded | Next | Return | Tails
  | AfterUpper | AfterLower | FullAdvance | TailAdvance | FrameSize
| PrefixLength | LastBias | IV (word:nat) | SwapMask (first:nat) | PublishMask
| KeyStart | KeyLimit | KeyIncrement | FinalRounds
| SaveLength (row:nat) | SpillRow (row:nat) | StoreDigest (row:nat)
| Full (lane:nat) | Empty (lane:nat) | Loaded (lane:nat).
Scheme Equality for label.
Inductive atom := Bytes (raw:list Z) | Label (l:label)
  | Rip (prefix:list Z) (literal:Z) | Branch (short:bool) (opcode:list Z) (l:label).
Definition width a := match a with
  | Bytes xs => length xs | Label _ => 0%nat | Rip xs _ => (length xs+4)%nat
  | Branch short xs _ => (length xs+(if short then 1 else 4))%nat end.
Fixpoint offset l code : nat := match code with
  | [] => 0%nat | Label q :: rest => if label_beq l q then 0%nat else offset l rest
  | x::rest => (width x + offset l rest)%nat end.
Fixpoint assemble (code_pc literal_pc:Z) (at_label:label->nat) at_pc body := match body with
  | [] => [] | x::rest =>
    let next := at_pc + Z.of_nat (width x) in
    (match x with
    | Bytes xs => xs | Label _ => []
    | Rip xs off => xs ++ le32 (literal_pc + off - (code_pc+next))
    | Branch short xs l => let disp := Z.of_nat (at_label l) - next in
        xs ++ (if short then [disp mod 256] else le32 disp) end) ++
    assemble code_pc literal_pc at_label next rest end.
Definition lanes {A} (f:nat->list A) := flat_map f (seq 0 8).

Definition prefix_row i :=
 let j:=Z.of_nat i in let reg:=8*j in
 [Bytes ([0xc5;0x7e;0x6f] ++
   (if j =? 0 then [6] else if j <? 4 then [0x46+reg;32*j] else [0x86+reg] ++ le32 (32*j)));
  Bytes (prefix 3 1 (8+j) (8+j) 2 ++ [0x3a] ++
   (if j =? 0 then [2] else [0x42+reg;j]) ++ [1])].
Definition entry :=
 [Bytes (exit_bytes PushRbp);
  Bytes (op_bytes (Program [] []) (MovReg 5 4) ++ op_bytes (Program [] []) AlignRsp64);
  Label FrameSize; Bytes (op_bytes (Program [] []) (AdjustRsp true 704));
  Bytes (op_bytes (Program [] []) (MovReg 9 1) ++ op_bytes (Program [] []) (MovReg 11 8));
  Bytes (rm_memory 1 2 0x6f 24 0 11 0);
  Rip (evex 1 1 25 24 5 true ++ [0xd4;0x0d]) 64; Label PrefixLength;
  Rip (evex 1 1 26 24 5 true ++ [0xd4;0x15]) 72; Label LastBias;
  Bytes (encode_vpsrlq 24 25 61 ++ encode_vpsllq 25 25 3 ++ encode_vpsrlq 26 26 7)] ++
 flat_map (fun i=>[Label (SaveLength i); Bytes (rm_memory 1 1 0x7f (24+i)%nat 0 4 (512+64*Z.of_nat i))]) (seq 0 3) ++
 lanes (fun i=>[Rip (prefix 2 1 (16+Z.of_nat i) 0 5 ++ [0x59;modrm 0 (Z.of_nat i) 5]) (128+8*Z.of_nat i); Label (IV i)]) ++
 lanes prefix_row ++ [Bytes [0x31;0xf6;0x45;0x31;0xc0]].

Definition transpose_code first := flat_map (fun ins=>match ins with
  | Mask => [Rip (prefix 1 1 8 0 5 ++ [0x6f;5]) 0; Label (SwapMask first)]
  | _ => [Bytes (Transpose.encode 0 ins)] end) (transpose first).
Definition round_code expanding := flat_map (fun i=>map (fun ins=>Bytes (Rounds.encode ins))
   (program expanding i)) (seq 0 16).
Definition with_mask k (xs:list Z) := match xs with
  | a::b::c::d::rest=>a::b::c::(d+k)::rest | _=>[] end.
Definition body :=
 [Label Block] ++ transpose_code 0 ++ [Branch false [0xe8] Rows; Label AfterUpper] ++ transpose_code 8 ++
 [Bytes (rr 2 1 0x7c 24 0 6);
  Bytes (rm_memory 2 1 0x29 4 24 4 640);
  Bytes (rm_memory 3 1 0x1e 5 24 4 640 ++ [1]);
  Bytes (with_mask 4 (rm_memory 1 1 0x6f 14 0 4 512));
  Bytes (with_mask 4 (rm_memory 1 1 0x6f 15 0 4 576))] ++
 lanes (fun i=>[Label (SpillRow i); Bytes (rm_memory 1 1 0x7f (16+i)%nat 0 4 (64*Z.of_nat i))]) ++
 [Label KeyStart; Rip [0x4c;0x8d;0x15] 192; Label KeyLimit; Rip [0x48;0x8d;0x15] (192+512); Label Expanded] ++
 round_code true ++
 [Label KeyIncrement; Bytes [0x49;0x81;0xc2;0x80;0;0;0;0x49;0x39;0xd2]; Branch false [0x0f;0x85] Expanded; Label FinalRounds] ++
 round_code false ++
 lanes (fun i=>[Bytes (rm_memory 1 1 0xd4 (16+i)%nat (16+i)%nat 4 (64*Z.of_nat i))]) ++
 [Bytes [0xc5;0xf8;0x98;0xe4]; Branch true [0x74] Next;
  Rip (prefix 1 1 25 0 5 ++ [0x6f;0x0d]) 0; Label PublishMask] ++
 lanes (fun i=>[Bytes (rr_w0 2 1 0 24 (16+i)%nat 25);
   Label (StoreDigest i); Bytes (with_mask 4 (rm_memory 1 2 0x7f 24 0 7 (64*Z.of_nat i)))]) ++
 [Label Next; Bytes [0xc5;0xf8;0x98;0xed]; Branch true [0x74] Return;
  Bytes [0x48;0xff;0xc6]; Branch false [0xe8] Rows; Label AfterLower; Branch false [0xe9] Block;
  Label Return; Bytes (op_bytes (Program [] []) (MovReg 4 5) ++ exit_bytes PopRbp ++
    op_bytes (Program [] []) ZeroUpper ++ exit_bytes Ret)].

Definition scalar_load op base (i:nat) :=
 [op;0x8b] ++ if Nat.eqb i 0 then [base] else [base+0x40;8*Z.of_nat i].
Definition full_row i := [0x62;0x11;0xfe;0x48;0x6f;4+8*Z.of_nat i;2].
Definition tail_row i :=
 let j:=Z.of_nat i in
 [Bytes (scalar_load 0x49 0x0b i ++ [0x4c;0x29;0xc1]); Branch true [0x72] (Empty i);
  Bytes (scalar_load 0x4d 0x11 i ++ [0x48;0x83;0xf9;0x40]); Branch true [0x73] (Full i);
  Bytes [0xb8;1;0;0;0;0x48;0xd3;0xe0;0xc4;0xe1;0xfb;0x92;0xc8;0x48;0xff;0xc8;
         0xc4;0xe1;0xfb;0x92;0xd0];
  Bytes [0x62;0x11;0x7f;0xca;0x6f;4+8*j;2];
  Bytes [0x62;0x11;0x7f;0x49;0x6f;0xc0+8*j]; Branch true [0xeb] (Loaded i);
  Label (Full i); Bytes (full_row i); Branch true [0xeb] (Loaded i);
  Label (Empty i); Bytes (rr_w0 1 1 0xef (8+i)%nat (8+i)%nat (8+i)%nat); Label (Loaded i)].
Definition rows :=
 [Label Rows; Bytes [0x49;0x8d;0x40;0x40]; Bytes (rr 2 1 0x7c 24 0 0);
  Bytes (rm_memory 3 1 0x1e 1 24 11 0 ++ [6]); Bytes [0xc5;0xf8;0x98;0xc9];
  Branch true [0x75] Tails] ++
 lanes (fun i=>[Bytes (scalar_load 0x4d 0x11 i ++ full_row i)]) ++
 [Label FullAdvance; Bytes [0x49;0x83;0xc0;0x40;0xc3]; Label Tails; Bytes [0xb8;0x80;0;0;0];
  Bytes (rr_w0 2 1 0x7a 24 0 0)] ++ lanes tail_row ++ [Label TailAdvance; Bytes [0x49;0x83;0xc0;0x40;0xc3]].
Definition listing := entry ++ body ++ rows.
Definition image pc ro := assemble pc ro (fun l=>offset l listing) 0 listing.

(* Truncation by le32 or the short-jump encoder must preserve the signed
   displacement. Both sides of a PC-relative reference share the load bias. *)
Fixpoint displacements pc ro at_pc code := match code with
  | [] => true | a::rest =>
    let next := at_pc+Z.of_nat (width a) in
    (match a with
     | Rip _ k => (-(2^31) <=? ro+k-(pc+next)) && (ro+k-(pc+next) <? 2^31)
     | Branch short _ l =>
       let disp:=Z.of_nat (offset l listing)-next in let limit:=if short then 128 else 2^31 in
       (-limit <=? disp) && (disp <? limit)
     | _ => true end) && displacements pc ro next rest end.
