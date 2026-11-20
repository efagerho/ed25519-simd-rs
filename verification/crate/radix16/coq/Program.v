From Coq Require Import List ZArith.
From Machine Require Import execution.Packed.
Import ListNotations.
Local Open Scope nat_scope.

Definition carry lo hi := [ShiftQ false 6 lo 52; AddQ hi hi 6].
Definition pack := [Imm true 0x8888888888888%Z; Broadcast false 5] ++
 map (fun i=>AddRow i 5 i) (seq 0 5) ++
 [ShiftQ true 8 1 52; ShiftQ true 9 2 40; ShiftQ true 10 3 28; ShiftQ true 11 4 16] ++
 carry 0 1 ++ [AddQ 0 0 8] ++ carry 1 2 ++ [ShiftQ false 1 1 12; AddQ 1 1 9] ++
 carry 2 3 ++ [ShiftQ false 2 2 24; AddQ 2 2 10; ShiftQ false 3 3 36; AddQ 3 3 11].
Definition expand w e o := [ShiftQ false 7 w 4; And 7 7 5; And w w 5;
 Sub 7 7 6; Sub w w 6; Unpack false e w 7; Unpack true o w 7].
Definition pair a b c d imm lane := [Shuffle 0 a b imm; Shuffle 1 c d imm;
 Shuffle 2 0 1 0x88; Shuffle 3 0 1 0xdd; Store lane 2; Store (lane+2) 3].
Definition tail := pack ++ [Imm false 15%Z; Broadcast true 5; Imm false 8%Z; Broadcast true 6] ++
 expand 0 8 9 ++ expand 1 10 11 ++ expand 2 12 13 ++ expand 3 14 15 ++
 pair 8 10 12 14 0x44 0 ++ pair 9 11 13 15 0x44 1 ++
 pair 8 10 12 14 0xee 4 ++ pair 9 11 13 15 0xee 5 ++ [Upper].
