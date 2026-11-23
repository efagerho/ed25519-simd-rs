From Coq Require Import List ZArith.
From Machine Require Import isa.X86 isa.Instructions execution.Blocks.
From Ed25519Simd.CachedAdd Require Import Program Kernels CarryHandoff CarryStores.
Import ListNotations. Local Open Scope Z_scope.

Definition vector_bytes := flat_map Instructions.encode.
Definition byte_slice (image:list Z) offset (expected:list Z) :=
  firstn (length expected) (skipn offset image) = expected.

(* CMP sets ZF, the intervening vector instructions preserve it, and JE
   skips precisely the left product's carry. Both paths meet at the right
   product. Register 1 denotes ECX in double4; 2 denotes EDX in cached add. *)
Definition pair_bytes reg tag :=
  vector_bytes (firstn 5 folded_product) ++ [0x83; modrm 3 7 reg; tag] ++
  vector_bytes (skipn 5 folded_product) ++ [0x74; Z.of_nat (length (vector_bytes normalize_left))] ++
  vector_bytes normalize_left ++ vector_bytes right_product ++ [0xc3].

Record carry_sites := Sites {
  double_pair : nat; add_pair : nat; prepare_ab : nat;
  call_cd : nat; compute_cd : nat; raw_c : nat;
  double_xz : nat; double_yt : nat; add_xz : nat; add_yt : nat
}.

Definition rel32_bytes opcode (pc target:nat) :=
  opcode :: le32 (Z.of_nat target - (Z.of_nat pc + 5)).

(* Check both the affine-side jump to the raw C product and the return site
   at F/G. DEC ECX followed by JNE takes the affine arm when ECX was 1. *)
Definition affine_bytes (s:carry_sites) :=
  let doubled := vector_bytes twice_z in
  let jump_pc := (compute_cd s + 4 + length doubled)%nat in
  [0xff;0xc9;0x75;Z.of_nat (length doubled + 5)] ++ doubled ++
  rel32_bytes 0xe9 jump_pc (raw_c s).

Definition store_bytes yt := flat_map (op_bytes add_cached_program) (point_stores yt).

Definition carry_blocks double_image add_image s : Prop :=
  ((Z.of_nat (length double_image) <? 2^31) && (Z.of_nat (length add_image) <? 2^31) &&
   Nat.ltb (length (vector_bytes normalize_left)) 128 && Nat.ltb (length (vector_bytes twice_z) + 5) 128)%bool = true /\
  byte_slice double_image (double_pair s) (pair_bytes 1 4) /\
  byte_slice add_image (add_pair s) (pair_bytes 2 3) /\
  byte_slice add_image (prepare_ab s) (vector_bytes (code PrepareAB)) /\
  byte_slice add_image (call_cd s)
    (rel32_bytes 0xe8 (call_cd s) (compute_cd s) ++ vector_bytes (code PrepareFG)) /\
  byte_slice add_image (compute_cd s) (affine_bytes s) /\
  byte_slice add_image (raw_c s) (vector_bytes affine_tail ++ [0xc3]) /\
  byte_slice double_image (double_xz s) (store_bytes false) /\
  byte_slice double_image (double_yt s) (store_bytes true) /\
  byte_slice add_image (add_xz s) (store_bytes false) /\
  byte_slice add_image (add_yt s) (store_bytes true).

(* After the two product calls, store their results into the same point
   and execute the next cached-add prologue on that memory. *)
Record carry_block_contract double_image add_image s : Prop := {
  linked_carry_blocks : carry_blocks double_image add_image s;
  stores_complete : forall yt, exists es, store_trace yt = Some (point_control,es);
  pair_products : forall defer r load, pair_semantics defer r load;
  next_addition : forall j rx lx ry ly r mem, stored_handoff_semantics j rx lx ry ly r mem;
  affine_sum_difference : forall r read, affine_semantics r read
}.

Theorem checked_carry_blocks double_image add_image s :
  carry_blocks double_image add_image s -> carry_block_contract double_image add_image s.
Proof.
  intro images; constructor; [exact images|apply stores_execute|apply paired_product_correct|
    apply stored_carry_handoff|apply affine_carry_handoff].
Qed.
