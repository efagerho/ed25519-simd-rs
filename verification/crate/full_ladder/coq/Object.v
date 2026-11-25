From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordBounds memory.MemoryGeometry memory.FlatMemory.
From Ed25519Simd.FullLadder Require Import LinkedBytes Program Operands Execution Native Composition Progress Audit.
From Ed25519Simd.FullLadder Require FirstStage.
Import ListNotations. Local Open Scope Z_scope.

Lemma checked_path full pad : In pad [8;24;40;56] -> run full pad=Some(schedule full).
Proof. intros [<-|[<-|[<-|[<-|[]]]]];destruct full;vm_compute;reflexivity. Qed.
Theorem assembled_full_ladder_correct : full_ladder_contract.
Proof.
 constructor.
 - split;[vm_compute;reflexivity|split;[vm_compute;reflexivity|]].
   cbv [images separate];repeat match goal with
   | |- _ /\ _=>split | |- Forall _ (_::_)=>constructor
   | |- Forall _ []=>constructor | |- True=>exact I end.
   all: unfold disjoint;vm_compute;intuition discriminate.
 - exact SO.assembled_stage_round_correct.
 - exact LO.assembled_ladder_step_correct.
 - intros slide s c P W M;destruct(loaded_images _ _ P _ _ (or_introl eq_refl)) as [Img [_ Apart]].
   destruct(loaded_images _ _ P _ _ (or_intror (or_introl eq_refl))) as [Stage _].
   pose proof(frame_range _ _ P) as Stack.
   assert (Code:54<Z.of_nat(length symbol_bytes)) by (vm_compute;reflexivity).
   assert (Target:0<Z.of_nat(length Ed25519Simd.StageRound.ObjectBytes.symbol_bytes)) by (vm_compute;reflexivity).
   eapply StageEntry.checked;try eassumption;unfold fits64,word64 in *;lia.
 - exact FirstStage.checked.
 - intros slide s v c P W Pt Stack Map.
   destruct(ladder_placement _ _ _ (child_layout _ _ P)) as [_ SA PA CA SF PF CF PS CS CP Code].
   destruct(loaded_images _ _ P _ _ (or_introl eq_refl)) as [_ [Separate _]].
   eapply NativeSeed.checked;[exact W|exact Pt|exact Stack|exact (conj PA PF)|split;[exact CA|]| |exact Map|].
   + unfold fits64 in *;lia.
   + unfold disjoint in *;lia.
   + intros x X;unfold SeedPath.region,disjoint in *;lia.
 - intros slide s full B A P Mode V Tables.
   pose proof (checked_path full _ (entry_alignment _ _ P)) as Trace.
   assert (IPs:forall e,direct e -> word64(slide+continuation e)).
   { destruct (loaded_images _ _ P _ _ (or_introl eq_refl)) as [Fit _].
     unfold fits64 in Fit;assert (N:Z.of_nat(length symbol_bytes)=885+setup_length) by (vm_compute;reflexivity).
     rewrite N in Fit;intros [n| | |f a row|f] D;try contradiction;
     unfold continuation,return_offset,word64;try destruct a;cbv [setup_length defer_double] in *;lia. }
   destruct(safe_exec _ _ _ _ _ _ _ _ (schedule_safe _ _ _ _ _ _ _ _
      (child_layout _ _ P) IPs V Tables full (ByteMemory.buffer_words (mem s) (regs s 7%nat)) (ByteMemory.buffer_words (mem s) (base_of s)))) as [[z R] All].
   split.
   + destruct z as [o c];exists o;split;[exact Mode|exists (schedule full),c;auto].
   + intros out [_ [ops [c [Path R']]]];rewrite Trace in Path;injection Path as <-.
     apply (schedule_correct _ _ _ _ _ V Tables _ _ _ _ _ (All _ R')).
Qed.
