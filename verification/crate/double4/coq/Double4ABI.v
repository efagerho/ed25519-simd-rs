From Coq Require Import List ZArith Bool.
From Machine Require Import execution.Blocks.
Import ListNotations. Open Scope Z_scope.
Definition scratch := 0%nat.
Definition point := 1%nat.
Definition abi_layout : layout := fun r cell =>
 if Nat.eqb r scratch then
   if (0 <=? cell) && (cell <? 20) then WriteVector
   else if cell =? -1 then ReturnWords 192
   else if cell =? 20 then ReturnWords 255 else Unmapped
 else if Nat.eqb r point && (0 <=? cell) && (cell <? 20) then WriteVector else Unmapped.
Definition initial_control incoming pad bp := Control (At 0)
 (fun r => match r with
 | 4%nat => Ptr (scratch,1288+pad) | 5%nat => Int bp
 | 7%nat => Ptr (point,0) | _ => gpr incoming r end)
 (zf incoming) (fun a=>if ptr_eq a (scratch,1288+pad) then Some Caller else return_memory incoming a).
Definition permitted_padding pad := In pad [0;16;32;48].
Definition limb_address region i : pointer := (region,64*Z.of_nat i).
Definition words_at (m:pointer -> vector) region k :=
 m (limb_address region (k/8)) (k mod 8)%nat.
From Machine Require Import execution.WordBounds.
Definition valid_double4_entry (initial:state) pad :=
 permitted_padding pad /\
 (exists incoming bp,word64 bp /\ fst initial=initial_control incoming pad bp) /\
 data_words(snd initial).
