From Coq Require Import List ZArith.
From Machine Require Import execution.Blocks execution.LayoutProofs execution.ScalarRefinement.
From Ed25519Simd.Double4 Require Import Program Double4ABI Double4Memory Double4Bytes Double4Spec.
From Ed25519Simd.Double4 Require Audit Logical FrameProof ReadFootprint ObjectBytes Round.
Definition object_bytes := ObjectBytes.symbol_bytes.
Lemma logical_execution size initial pad : valid_double4_entry initial pad ->exists final,
 returns double4_program abi_layout initial final /\stack_restored initial final /\
 registers_preserved initial final /\memory_safe double4_program size pad initial final /\
 output_initialized double4_program initial final /\
 double4_spec(words_at(memory(snd initial))point)(words_at(memory(snd final))point).
Proof.
 intro Entry;destruct(Logical.double4_returns_correct _ _ Entry)as[final[R[SP Spec]]].
 destruct(FrameProof.double4_frame_correct size _ _ _ Entry R)as[Regs[Mem Init]].
 exists final;split;[exact R|];split;[exact SP|];split;[exact Regs|];split;[exact Mem|];split;assumption.
Qed.
Theorem assembled_double4_correct : Audit.double4_contract object_bytes.
Proof.
 constructor.
 - vm_compute; reflexivity.
 - exact Round.block_layout_checked.
 - apply concrete_contract_from_logical; [apply logical_execution|apply ReadFootprint.input_t_unread_correct].
Qed.
Print Assumptions assembled_double4_correct.
