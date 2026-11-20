From Coq Require Import List ZArith Bool.
From Machine Require Import isa.IndexedLoad execution.IndexedLoads execution.Packed execution.LinkedCalls.
Import ListNotations. Local Open Scope nat_scope.

Inductive operand := Odd | Base | Even.
Definition prefix := [LeaTwice 1 9; LeaTwice 8 9].
Definition direct r n := Addr r false (Z.of_nat n).
Definition affine n := Addr 2 true (Z.of_nat n).
Definition half d a (upper:bool) := if upper then InsertY d d a true else LoadY d a.

Definition load_lane kind lane :=
  let upper := Nat.leb 2 (lane mod 4) in
  let a := lane mod 2 + 2*(lane/4) in
  let b := a+4 in let c := a+8 in let full := 16+lane in
  match kind with
  | Base =>
      [MovZX true (direct 1 (64*lane)); CopyEaxToR11d; ShrR11d 4;
       And32 0 15; And32 11 240; OrEaxR11d; XorEax 136; ImulEax 120;
       LoadZ full (affine 0); half a (affine 64) upper; half b (affine 88) upper]
  | _ =>
      [MovZX false (direct 8 (64*lane + match kind with Odd=>1 | _=>0 end));
       And32 0 15; XorEax 7; ImulEax 160; AddRax (direct 6 (8*lane));
       half a (direct 0 160) upper; half b (direct 0 192) upper;
       LoadZ full (direct 0 224); half c (direct 0 288) upper]
  end.
Definition load_block kind := flat_map (load_lane kind) (seq 0 8).

Definition four r dst (skip:bool) :=
  [UnpackQ false 24 r (r+1); UnpackQ false 25 (r+2) (r+3)] ++
  (if skip then [] else [Shuffle 26 24 25 0x88; StoreAligned dst 26]) ++
  [Shuffle 27 24 25 0xdd; StoreAligned (dst+2) 27;
   UnpackQ true 24 r (r+1); UnpackQ true 25 (r+2) (r+3);
   Shuffle 26 24 25 0x88; Shuffle 27 24 25 0xdd;
   StoreAligned (dst+1) 26; StoreAligned (dst+3) 27].
Definition blocks sel dst :=
  [Shuffle 28 24 25 sel; Shuffle 29 26 27 sel;
   Shuffle 30 28 29 0x88; Shuffle 31 28 29 0xdd;
   StoreAligned dst 30; StoreAligned (dst+4) 31].
Definition parity high dst :=
  [UnpackQ high 24 16 17; UnpackQ high 25 18 19;
   UnpackQ high 26 20 21; UnpackQ high 27 22 23] ++
  blocks 0x88 dst ++ blocks 0xdd (dst+2).
Definition route kind :=
  let dst := match kind with Odd=>0 | Base=>20 | Even=>35 end in
  match kind with
  | Base => parity false dst ++ parity true (dst+1) ++ four 0 (dst+8) false ++ four 4 (dst+11) true
  | _ => four 0 dst false ++ four 4 (dst+4) false ++
         parity false (dst+8) ++ parity true (dst+9) ++ four 8 (dst+16) false
  end.

Definition operands := [Odd; Base; Even].
Definition encode_phase k :=
  flat_map IndexedLoad.encode (load_block k) ++ flat_map Packed.encode (route k).
Definition image := flat_map IndexedLoad.encode prefix ++ flat_map encode_phase operands ++
                    Packed.encode Upper ++ encoding 0 Return.
Definition valid_code := forallb IndexedLoad.valid prefix &&
  forallb (fun k => forallb IndexedLoad.valid (load_block k) &&
                    forallb (Packed.valid_with_alignment true 55) (route k)) operands.
Definition phase s k := Packed.execute 55 (route k) (IndexedLoads.execute (load_block k) s).
Definition body s := fold_left phase operands (IndexedLoads.execute prefix s).
Definition run pc s := caller_step 0 (pc+Z.of_nat (length image)-1)%Z Return
                         (Packed.execute 55 [Upper] (body s)).
