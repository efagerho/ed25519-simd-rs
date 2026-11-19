From Machine Require Import LayoutProofs.
From Coq Require Import List ZArith.
From Machine Require Import Blocks.
Require Import Program Double4ABI Double4Memory Double4Bytes Double4Spec.

(* This is the complete public contract. Its arithmetic specification is four
   applications of Double4Spec.doubling, independently in all eight lanes. *)
Definition double4_contract (symbol_bytes : list Z) : Prop :=
 (* The modeled instructions encode exactly the bytes in the linked symbol. *)
 image double4_program = symbol_bytes /\
 valid_program double4_program = true /\
  program_layout double4_program /\
 (forall initial pad, valid_double4_entry initial pad -> exists final,
  (* Finite execution, normal return, restored RSP and SysV saved registers. *)
  returns double4_program abi_layout initial final /\
  stack_restored initial final /\
  registers_preserved initial final /\
  (* One shared byte memory covers vectors, the saved RBP and all return
     addresses. Writes stay in the point or the private stack interval;
     caller return bytes and all other bytes are preserved. *)
  memory_safe double4_program (Z.of_nat (length symbol_bytes)) pad initial final /\
  (* Every output byte is written; no instruction reads the incoming T. *)
  output_initialized double4_program initial final /\
  input_t_unread double4_program initial final /\
  (* X/Y/Z may be loose; T is arbitrary. No curve-membership assumption.
     All four output coordinates satisfy the public limb bounds. *)
  double4_spec (words_at (memory (snd initial)) point)
               (words_at (memory (snd final)) point)) /\
 (* This constructs the logical entry from actual qwords and a single byte
    array. Reads agree exactly at every trace prefix. It also proves that
    the modeled relative alignment equals x86 AND RSP,-64 at that placement. *)
 concrete_double4_contract double4_program (Z.of_nat (length symbol_bytes)).
