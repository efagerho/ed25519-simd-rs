From Coq Require Import List ZArith Lia.
From Curve25519.group Require Import Representation.
From Machine Require Import memory.FlatMemory execution.LinkedCalls.
From Ed25519Simd.LadderStep Require Import LinkedBytes Callees Schedule Audit Calls Execution.
From Ed25519Simd.Double4 Require Object.
From Ed25519Simd.CachedAdd Require Object.

Theorem assembled_ladder_step_correct : ladder_contract.
Proof.
 constructor.
 - vm_compute; reflexivity.
 - exact (Ed25519Simd.Double4.Audit.code_matches Ed25519Simd.Double4.Object.assembled_double4_correct).
 - exact (Ed25519Simd.CachedAdd.Audit.code_matches Ed25519Simd.CachedAdd.Object.assembled_cached_add_correct).
 - exact linked_regions_separate.
 - intros slide scratch pad point cache full s Place W SP Pt Cache Mode B Odd Base Even.
   destruct (execute _ _ _ _ _ _ _ Place W SP Pt Cache Mode B Odd Base Even)
     as [out [Run [Stack [Saved [Frame [Bounds [Values T]]]]]]].
   cbv zeta; exists out; rewrite SP; constructor.
   + exact Run.
   + intros ip other Other; eapply runs_unique; [apply dispatch_unique|exact Other|exact Run].
     assert (double4_pc<>cached_pc) by (vm_compute;discriminate);lia.
   + now rewrite SP.
   + exact Saved.
   + exact Frame.
   + exact Bounds.
   + exact Values.
   + exact T.
   + intros j P O Bp E Lane Repr OddCache BaseCache EvenCache.
     eapply represents_equivalent; [exact (Values j Lane)|].
     now apply ladder_represents.
Qed.
Print Assumptions assembled_ladder_step_correct.
