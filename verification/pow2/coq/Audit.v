From Coq Require Import List ZArith.
From Machine Require Blocks.
Require Import Program Pow2ABI Pow2Memory FieldSpec.

Definition pow2_contract (symbol_bytes : list Z) : Prop :=
  (* Encoding the modeled program gives the exact symbol bytes, including padding. *)
  Blocks.image pow2_program = symbol_bytes /\
  (* The operands are encodable, the layout is contiguous, and all static
     call, jump, and fallthrough targets start a basic block. *)
  Blocks.valid_program pow2_program = true /\
  (* Every call that satisfies the entry convention reaches a final state
     with the properties below. *)
  forall initial a b, valid_pow2_entry initial a b ->
    exists final,
      (* Execution returns to the caller in finitely many modeled steps. *)
      Blocks.returns pow2_program abi_layout initial final /\
      (* After the return, RSP is eight bytes above its value at entry. *)
      stack_restored initial final /\
      (* RBX, RBP and R12 through R15 have their entry values on return. *)
      registers_preserved initial final /\
      (* For every valid address placement, each store stays in the 640-byte
         output or in [entry RSP - 1936, entry RSP - 8). Each CALL writes a
         free private slot. Every RET reads its own saved address from the
         shared byte memory, including the caller's original return address. *)
      memory_safe pow2_program (Z.of_nat (List.length symbol_bytes)) initial final /\
      (* If all input limbs are in [0, 2^52), each lane value x in a or b
         gives a result congruent to x^(2^252 - 3) modulo (2^255 - 19) in
         the first or second output half, respectively, at the entry RDI pointer.
         All output limbs are nonnegative. Limb 1 is at most 2^51 + 511 and
         the other four are below 2^51. *)
      pow2_spec a b (output_words initial final).
