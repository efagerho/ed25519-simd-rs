From Coq Require Import List ZArith NArith Strings.Byte Bool Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.WordSemantics
 execution.WordBounds abi.SysV memory.FlatMemory memory.ByteMemory.
From SHA512 Require Import Spec.
From Ed25519Simd.Sha512Challenge Require Import Compression Block Loader Lanes Frame Output Image Rows Control.
Import ListNotations.
Local Open Scope Z_scope.

Definition get_state (read:nat->N) := State (read 0%nat) (read 1%nat) (read 2%nat) (read 3%nat)
                                          (read 4%nat) (read 5%nat) (read 6%nat) (read 7%nat).
Definition reload s m j := get_state (fun r=>Z.to_N (read_word m (cell (frame s) r j))).
Definition last s m j := Z.to_nat (length_slot s m 2 j).
Definition finish_mask s m t j := Nat.eqb t (last s m j).
Definition continuing s m t := existsb (fun j=>(t <? last s m j)%nat) (seq 0 8).
Definition hash_step table s saved t cursor hs j :=
  let tail := big_endian 8 (Z.to_N (length_slot s saved 0 j)) ++
              big_endian 8 (Z.to_N (length_slot s saved 1 j)) in
  let block := native_block s saved t cursor j (finish_mask s saved t j) tail in
  feed (reload s saved j) (working_with table (hs j) block).

(* Byte address within eight masked VMOVDQU64 row stores. Inactive qwords
   keep their previous memory, even when their registers run further rounds. *)
Definition stores s m t hs x :=
  let delta:=x-dst s in
  let j:=Z.to_nat (delta mod 64/8) in
  if (0 <=? delta) && (delta <? 512) && finish_mask s m t j then
    Z.of_N (Byte.to_N (nth (Z.to_nat (8*(delta/64)+delta mod 8)) (emit (hs j)) x00))
  else m x.

(* The internal leaf only reads caller memory. The near call leaves its
   continuation in the qword immediately below the aligned private frame. *)
Definition call_rows s m ip :=
  let ret:=frame s-8 in let pushed:=store_word m ret ip in
  if read_word pushed ret =? ip then Some pushed else None.

Fixpoint blocks fuel table s (upper lower:Z) stride t cursor hs m := match fuel with
| O => None
| S n =>
  match call_rows s m upper with None=>None | Some back =>
    let saved:=spill_frame back s hs in
    let work:=hash_step table s saved t cursor hs in let next:=stores s saved t work in
    if continuing s saved t then
      match call_rows s next lower with None=>None | Some back'=>
        blocks n table s upper lower stride (S t) (cursor+stride+stride)%nat work back' end
    else Some next end end.

Record observation := Returned { return_ip:Z; return_sp:Z; saved_register:nat->option Z; after:bytes }.
Definition restored s m :=
  let rs:=put (regs s) 4 (sp s-8) in                  (* MOV RSP,RBP *)
  let popped:=stack_step 0 0 (PopRegister 5) rs m in
  let ret:=stack_step 0 0 NearReturn (result_regs popped) (result_mem popped) in
  Returned (target_ip ret) (result_regs ret 4%nat)
    (fun r=>if in_dec Nat.eq_dec r sysv_saved then Some (result_regs ret r) else None) (result_mem ret).
Definition literal_words m addr n :=
  map (fun i=>Z.to_N (read_word m (addr+8*Z.of_nat i))) (seq 0 n).
Definition initial_at m ro := get_state (fun r => nth r (literal_words m (ro+128) 8) 0%N).
Definition group_constants m slide groups := flat_map (fun addr=>literal_words m (slide+addr) 16) groups.
Definition enter s frame_size :=
 let saved:=push s (regs s 5%nat) in
 let bp:=regs saved 4%nat in
 let base:=WordSemantics.word (Z.land bp (-64)-frame_size) in
 matrix (mem saved) (base+512) 3 (length_value s).

Definition run pc code slide ro s :=
 if loads_match pc ro code then match decode pc code with
 | None => None
 | Some p => option_map (restored s)
   (blocks (S (maximum (challenge_input s))) (group_constants (mem s) slide (keys p)) s
     (slide+upper p) (slide+lower p) (row_step p) 0 0 (fun _=>initial_at (mem s) (slide+ro)) (enter s (depth p)))
 end else None.
