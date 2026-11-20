From Coq Require Import List ZArith Bool.
From Machine Require Import SysV Blocks.
Open Scope Z_scope.

(* Region origins are the first byte of each ABI buffer and the bottom of the
   allocated frame. A return address is a distinct qword in the same stack. *)
Definition input_a := 1%nat.
Definition input_b := 2%nat.
Definition output := 3%nat.
Definition stack := 4%nat.
Definition abi_layout (r:nat) (cell:Z) : permission :=
 if Nat.eqb r stack then
   if (0 <=? cell) && (cell <? 30) then WriteVector
   else if cell =? -1 then ReturnWords 128
   else if cell =? 30 then ReturnWords 2 else Unmapped
 else if Nat.eqb r output then
   if (0 <=? cell) && (cell <? 10) then WriteVector else Unmapped
 else if (Nat.eqb r input_a || Nat.eqb r input_b) && (0 <=? cell) && (cell <? 5)
      then ReadVector else Unmapped.
Definition initial_control (incoming:control) := Control (At 0)
 (fun r => match r with
 | 4%nat => Ptr (stack,1928) | 7%nat => Ptr (output,0)
 | 6%nat => Ptr (input_a,0) | 2%nat => Ptr (input_b,0) | _ => Blocks.gpr incoming r end)
 (zf incoming) (fun a => if ptr_eq a (stack,1928) then Some Caller else return_memory incoming a).

Definition limb_address (region:nat) (base:Z) (i:nat) : pointer :=
 (region,base + 64*Z.of_nat i).

Definition words_at (m:pointer -> vector) region k :=
 m (limb_address region 0 (k / 8)) (k mod 8)%nat.
Definition entry_buffers (s:data) a b :=
 (forall k, (k<40)%nat -> words_at (memory s) input_a k = a k) /\
 (forall k, (k<40)%nat -> words_at (memory s) input_b k = b k).

(* Incoming caller-saved values, vector registers, scratch and output storage
   are arbitrary. The logical regions describe the disjoint ABI memory views. *)
Definition valid_pow2_entry (initial:state) a b :=
 (exists incoming, fst initial = initial_control incoming) /\ entry_buffers (snd initial) a b.
Definition output_words (initial final:state) k :=
 match Blocks.gpr (fst initial) 7%nat with
 | Ptr addr => memory (snd final) (Blocks.offset addr (64*Z.of_nat (k/8))) (k mod 8)%nat
 | _ => 0 end.

Definition stack_restored := SysV.restores_rsp.
