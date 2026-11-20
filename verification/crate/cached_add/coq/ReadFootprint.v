From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.Blocks memory.MemoryTrace execution.ExecutionProperties.
From Ed25519Simd.CachedAdd Require Import Program CachedAddABI CachedAddMemory Control FrameProof.
Import ListNotations. Open Scope Z_scope.
Definition cache_reads_bounded affine a := negb(Nat.eqb(fst a)cached) ||
 ((0<=?snd a)&&(snd a+64<=?cache_length affine)).
Lemma read_footprint_checked full affine : forallb(cache_reads_bounded affine)
 (flat_map(read_addresses add_cached_program)(expected_path full affine))=true.
Proof. destruct full,affine;vm_compute;reflexivity. Qed.
Definition cache_contract affine initial final :=
 (forall off,memory(snd final)(cached,off)=memory(snd initial)(cached,off)) /\
 exists fuel es,record_path fuel add_cached_program(abi_layout affine)(fst initial)=Some(fst final,es) /\
 forall a,In a(flat_map(read_addresses add_cached_program)(data_effects es)) ->fst a=cached ->
 0<=snd a /\ snd a+64<=cache_length affine.
Theorem cache_correct initial pad full affine final : valid_cached_add_entry initial pad full affine ->
 returns add_cached_program(abi_layout affine)initial final ->cache_contract affine initial final.
Proof.
 intros Entry Returns;split.
 - intro off;apply(proj1(execution_memory_frame _ _ _ _ (proj1 Returns)(cached,off))).
   unfold vector_ok,access,abi_layout,cached,point,scratch;cbn [fst snd Nat.eqb andb].
   destruct ((0<=?off/64)&&(off/64<?cache_length affine/64));cbn;apply andb_false_r.
 - destruct initial as[c d];destruct Entry as[Pad[[incoming[bp[BP Init]]]_]];cbn [fst]in Init;subst c.
   pose proof(frame_checked full affine incoming pad bp Pad BP)as Frame.
   destruct(record_path 200 add_cached_program(abi_layout affine)(initial_control incoming pad bp full affine))as[[last es]|]eqn:R;[|discriminate].
   destruct(record_path_sound _ _ _ _ _ _ R)as[P _].
   pose proof(path_returns _ _ _ _ _ _ P d)as Ends.
   pose proof(return_unique _ _ _ _ _ Returns Ends)as ->.
   exists 200%nat,es;split;[exact R|].
   pose proof(control_path_checked incoming pad bp full affine Pad)as Check;rewrite P in Check.
   cbn [observe_path]in Check;injection Check as _ _ Ops;rewrite Ops.
   intros a Member Region;pose proof(read_footprint_checked full affine)as Read.
   rewrite forallb_forall in Read;specialize(Read a Member);unfold cache_reads_bounded in Read.
   rewrite Region,Nat.eqb_refl in Read;cbn in Read;apply andb_true_iff in Read as[L U];
   apply Z.leb_le in L;apply Z.leb_le in U;auto.
Qed.
