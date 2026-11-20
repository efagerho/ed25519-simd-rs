From Machine Require Import execution.LayoutProofs execution.ScalarRefinement.
From Coq Require Import List ZArith.
From Machine Require execution.Blocks.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Pow2 Require Import Program Pow2ABI Pow2Memory Pow2Bytes Pow2Spec.

Definition pow2_contract (symbol_bytes : list Z) : Prop :=
  (* Encoding the modeled program gives the exact symbol bytes, including padding. *)
  Blocks.image pow2_program = symbol_bytes /\
  (* The operands are encodable, the layout is contiguous, and all static
     call, jump, and fallthrough targets start a basic block. *)
  Blocks.valid_program pow2_program = true /\
  program_layout pow2_program /\
  (* Scalar operations refine qword semantics under explicit alignment and
     stack-byte premises; this is not independent ISA refinement. *)
  scalar_model_refinement pow2_program /\
  (* Every call that satisfies the entry convention reaches a final state
     with the properties below. *)
  (forall initial a b, valid_pow2_entry initial a b ->
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
      (* All 640 bytes at the entry RDI pointer are written before returning,
         independently of the input limb bounds or previous output contents. *)
      output_initialized pow2_program initial final /\
      (* If all input limbs are in [0, 2^52), each lane value x in a or b
         gives a result congruent to x^(2^252 - 3) modulo (2^255 - 19) in
         the first or second output half, respectively, at the entry RDI pointer.
         All output limbs are nonnegative. Limb 1 is at most 2^51 + 511 and
         the other four are below 2^51. *)
      pow2_spec a b (output_words initial final)) /\
  (* A concrete ABI entry constructs its logical views from one byte array.
     Every represented integer/vector word stays in [0, 2^64). At each trace
     prefix, decoding vector bytes gives exactly the logical qwords. All
     output bytes are written before return, the final output bytes satisfy
     the same field specification, and bytes outside the permitted
     output/stack writes are preserved. Initial byte
     agreement is proved by construction, not assumed by the caller. *)
  concrete_pow2_contract pow2_program (Z.of_nat (List.length symbol_bytes)).
