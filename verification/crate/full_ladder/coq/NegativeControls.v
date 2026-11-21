From Coq Require Import ZArith List.
From Ed25519Simd.FullLadder Require Import LinkedBytes Seed Program.
Import ListNotations.

(* Each mutation has the same instruction length as its original. Exercise
   the control or arithmetic check even if the byte witness changes with it. *)
Definition mutated change := walk (layout entry_pc (map change code)) 600 8 entry_pc (initial true).
Example final_t_loaded_from_wrong_slot :
 mutated (fun op=>match op with Reload false d b _=>Reload false d b (-48) | _=>op end)
 <> Some (schedule true).
Proof. vm_compute;discriminate. Qed.
Example wrong_pair_index :
 mutated (fun op=>match op with Lea8 9 15 _=>Lea8 9 15 0 | _=>op end) <> Some (schedule true).
Proof. vm_compute;discriminate. Qed.
Example wrong_frame :
 mutated (fun op=>match op with Allocate _=>Allocate 3456|_=>op end) <> Some (schedule true).
Proof. vm_compute;discriminate. Qed.
Example dropped_seed_fold :
 let a:=fun _:nat=> (2^52-1)%Z in let s:=Seed.Lane 0 (fun _=>0%Z) (fun _=>0%Z) in
 Seed.out (fold_left (Seed.step a)
   (map (fun op=>match op with Seed.Imm false _=>Seed.Imm false 0|_=>op end) Seed.code) s) 0
 <> Seed.result a 0 0.
Proof. vm_compute;discriminate. Qed.
