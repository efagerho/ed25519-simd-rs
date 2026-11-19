From Coq Require Import List ZArith.
From Machine Require Import Blocks LayoutProofs ScalarRefinement.
Require Import Program CachedAddABI CachedAddMemory CachedAddBytes CachedAddSpec.
Require Audit Logical FrameProof ReadFootprint ObjectBytes Control.
Definition object_bytes := ObjectBytes.symbol_bytes.
Local Lemma logical_execution size full affine initial pad : valid_cached_add_entry initial pad full affine ->exists final,
 returns add_cached_program(abi_layout affine)initial final /\stack_restored initial final /\
 registers_preserved initial final /\memory_safe affine add_cached_program size pad initial final /\
 output_initialized affine add_cached_program initial final /\
 cached_add_spec full affine(words_at(memory(snd initial))point)(words_at(memory(snd initial))cached)
 (words_at(memory(snd final))point).
Proof.
 intro Entry;destruct(Logical.cached_add_returns_correct _ _ _ _ Entry)as[final[R[SP Spec]]].
 destruct(FrameProof.cached_add_frame_correct full affine size _ _ _ Entry R)as[Regs[Mem Init]].
 exists final;split;[exact R|];split;[exact SP|];split;[exact Regs|];split;[exact Mem|];split;assumption.
Qed.
Theorem assembled_cached_add_correct : Audit.cached_add_contract object_bytes.
Proof.
 split;[vm_compute;reflexivity|];split;[exact Control.block_layout_checked|];
 split;[apply valid_program_sound;exact Control.block_layout_checked|];
 split;[apply scalar_model_refinement_checked|];split.
 - intros full affine initial pad Entry.
   destruct(logical_execution(Z.of_nat(length object_bytes)) full affine _ _ Entry)as[final[R[SP[Regs[Mem[Init Spec]]]]]].
   exists final;split;[exact R|];split;[exact SP|];split;[exact Regs|];split;[exact Mem|];split;[exact Init|];split;
   [eapply ReadFootprint.cache_correct;eassumption|exact Spec].
 - intros full affine;apply concrete_contract_from_logical,logical_execution.
Qed.
Print Assumptions assembled_cached_add_correct.
