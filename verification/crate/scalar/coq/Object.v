From Coq Require Import List ZArith.
From Machine Require Import execution.Blocks execution.LayoutProofs execution.ScalarRefinement.
From Ed25519Simd.Scalar Require Import Program ScalarABI ScalarSpec ScalarMemory ScalarBytes.
From Ed25519Simd.Scalar Require Audit Logical FrameProof ObjectBytes Control.
Definition object_bytes := ObjectBytes.symbol_bytes.
Local Lemma logical_execution size initial : valid_scalar_entry initial ->exists final,
 returns scalar_program abi_layout initial final /\stack_restored initial final /\
 registers_preserved initial final /\memory_safe scalar_program size initial final /\
 output_initialized scalar_program initial final /\
 scalar_spec(words_at(memory(snd initial))input)(words_at(memory(snd final))output).
Proof.
 intro Entry;destruct(Logical.scalar_returns_correct _ Entry)as[final[R[SP Spec]]].
 destruct(FrameProof.scalar_frame_correct size _ _ Entry R)as[Regs[Mem Init]].
 exists final;split;[exact R|];split;[exact SP|];split;[exact Regs|];split;[exact Mem|];split;assumption.
Qed.
Theorem assembled_scalar_correct : Audit.scalar_contract object_bytes.
Proof.
 split;[vm_compute;reflexivity|];split;[exact Control.block_layout_checked|];
 split;[apply valid_program_sound;exact Control.block_layout_checked|];
 split;[apply scalar_model_refinement_checked|];split.
 - apply logical_execution.
 - apply concrete_contract_from_logical,logical_execution.
Qed.
Print Assumptions assembled_scalar_correct.
