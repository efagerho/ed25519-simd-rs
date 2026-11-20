From Coq Require Import List ZArith Lia.
From Machine Require Import FlatMemory LinkedCalls.
Require Import LinkedBytes Callees Schedule Audit Calls Execution.
From Double4 Require Object.
From CachedAdd Require Object.

Theorem assembled_ladder_step_correct : ladder_contract.
Proof.
 split;[vm_compute;reflexivity|].
 split;[exact (proj1 Double4.Object.assembled_double4_correct)|].
 split;[exact (proj1 CachedAdd.Object.assembled_cached_add_correct)|].
 split;[exact linked_regions_separate|].
 intros slide scratch pad point cache full s Place W SP Pt Cache Mode.
 intros B Odd Base Even.
 destruct(execute _ _ _ _ _ _ _ Place W SP Pt Cache Mode B Odd Base Even)
   as [out [Run Post]].
 cbv zeta;exists out;rewrite SP;split;[exact Run|];split;[|exact Post].
 intros ip other Other;eapply runs_unique;[apply dispatch_unique|exact Other|exact Run].
 assert (double4_pc<>cached_pc) by (vm_compute;discriminate);lia.
Qed.
Print Assumptions assembled_ladder_step_correct.
