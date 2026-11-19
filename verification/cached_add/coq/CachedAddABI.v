From Coq Require Import List ZArith Bool.
From Machine Require Import Blocks WordBounds.
Import ListNotations. Open Scope Z_scope.
Definition scratch := 0%nat.
Definition point := 1%nat.
Definition cached := 2%nat.
Definition cache_length (affine:bool) := if affine then 960 else 1280.
Definition abi_layout (affine:bool) : layout := fun r cell =>
 if Nat.eqb r scratch then
   if (0 <=? cell) && (cell <? 20) then WriteVector
   else if cell =? -1 then ReturnWords 192
   else if cell =? 20 then ReturnWords 255 else Unmapped
 else if Nat.eqb r point && (0 <=? cell) && (cell <? 20) then WriteVector
 else if Nat.eqb r cached && (0 <=? cell) && (cell <? cache_length affine/64) then ReadVector
 else Unmapped.
Definition flag_word (flag:bool) : Z := if flag then 1 else 0.
Definition initial_control incoming pad bp full affine := Control (At 0)
 (fun r => match r with
 | 1%nat => Int(flag_word affine) | 2%nat => Int(flag_word full)
 | 4%nat => Ptr (scratch,1288+pad) | 5%nat => Int bp
 | 6%nat => Ptr (cached,0) | 7%nat => Ptr (point,0) | _ => gpr incoming r end)
 (zf incoming) (fun a=>if ptr_eq a (scratch,1288+pad) then Some Caller else return_memory incoming a).
Definition permitted_padding pad := In pad [0;16;32;48].
Definition limb_address region i : pointer := (region,64*Z.of_nat i).
Definition words_at (m:pointer -> vector) region k :=
 m (limb_address region (k/8)) (k mod 8)%nat.
Definition valid_cached_add_entry (initial:state) pad full affine :=
 permitted_padding pad /\
 (exists incoming bp,word64 bp /\ fst initial=initial_control incoming pad bp full affine) /\
 data_words(snd initial).
