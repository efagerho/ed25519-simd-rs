From Ed25519Simd.CachedAdd Require Import CarryImage CandidateDouble CandidateAdd CandidateSites.

Theorem linked_deferred_carry_correct :
  carry_block_contract CandidateDouble.symbol_bytes CandidateAdd.symbol_bytes CandidateSites.sites.
Proof.
  apply checked_carry_blocks. unfold carry_blocks.
  repeat apply conj; first [solve [vm_compute; reflexivity] | fail 1 "linked carry block mismatch"].
Qed.
