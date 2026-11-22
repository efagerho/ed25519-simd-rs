From Coq Require Import List ZArith.
From Machine Require Import execution.Packed.
From Ed25519Simd Require Import Radix16Output.
Import ListNotations.
Local Open Scope nat_scope.

Definition carry lo hi := [ShiftQ false 6 lo 52; AddQ hi hi 6].
Definition pack := [Imm true 0x8888888888888%Z; Broadcast false 5] ++
 map (fun i=>AddRow i 5 i) (seq 0 5) ++
 [ShiftQ true 8 1 52; ShiftQ true 9 2 40; ShiftQ true 10 3 28; ShiftQ true 11 4 16] ++
 carry 0 1 ++ [AddQ 0 0 8] ++ carry 1 2 ++ [ShiftQ false 1 1 12; AddQ 1 1 9] ++
 carry 2 3 ++ [ShiftQ false 2 2 24; AddQ 2 2 10; ShiftQ false 3 3 36; AddQ 3 3 11].
Definition tail := pack ++ write_digits ++ [Upper].
