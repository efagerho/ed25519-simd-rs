From Ed25519Simd Require Import PointResults.
From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordBounds execution.WordSemantics
 memory.FlatMemory memory.ByteMemory memory.MemoryGeometry abi.CallFrame.
From Ed25519Simd.FullLadder Require Import Program Operands Execution.
From Ed25519Simd.LadderStep Require Import Callees.
From Ed25519Simd.LadderStep Require Audit Object.
From Ed25519Simd.Double4 Require Double4Memory Double4Spec.
From Ed25519Simd.CachedAdd Require CachedAddMemory CachedAddSpec CachedAddABI.
From Ed25519Simd Require Import Wide51.
Import ListNotations. Local Open Scope Z_scope.
Module LA := Ed25519Simd.LadderStep.Audit.
Module LO := Ed25519Simd.LadderStep.Object.
Definition bits := CachedAddABI.flag_word.
Definition child_pc e := match e with DoubleFour=>L.double4_pc | Cached f a _=>add_target L.cached_pc f a
 | Ladder _=>L.wrapper_pc | _=>LinkedBytes.stage_pc end.
Definition child_image e := match e with DoubleFour=>L.double4_pc | Cached _ _ _=>L.cached_pc | _=>child_pc e end.
Definition offset_words m base row k : buffer_words m (base+64*Z.of_nat row) k =
 slice (buffer_words m base) row k.
Proof. unfold buffer_words,slice;f_equal;rewrite Nat2Z.inj_add,Nat2Z.inj_mul;ring. Qed.

(* The continuation addresses are offsets within the outer symbol, checked
   when the control interpreter follows each encoded CALL. *)
Definition continuation e := LinkedBytes.entry_pc + Program.return_offset e.
Definition footprint e := match e with
 | Cached _ a _=>if a then 15%nat else 20%nat | _=>55%nat end.
Definition child_regs pt base e (other:nat->Z) :=
 let rs := Instructions.put (Instructions.put other 4 (base-8)) 7 pt in
 match e with
 | Cached f a row=>let args:=Instructions.put rs 6 (base+64*Z.of_nat row) in
   if defer_add f a then args else Instructions.put (Instructions.put args 2 (bits f)) 1 (bits a)
 | Ladder f=>Instructions.put (Instructions.put rs 6 base) 2 (bits f)
 | _=>rs end.

Definition child_run slide base e entry ip out :=
 match e with
 | DoubleFour | Cached _ _ _=>dispatch (slide+L.double4_pc) (slide+L.cached_pc)
     (base-1344) 48 (slide+child_pc e) entry ip out
 | Ladder _=>runs (dispatch (slide+L.double4_pc) (slide+L.cached_pc) (base-1344) 16)
    slide L.wrapper_pc LA.program entry ip out
 | _=>False end.

Record arena slide pt base : Prop := {
 ladder_placement : LA.placement_ok slide (base-1344) 16 pt base;
 direct_code : forall e, e=DoubleFour \/ (exists f a row,e=Cached f a row) ->
   WordBounds.word64 (slide+continuation e) /\
   ~(slide+child_image e<=slide+continuation e<slide+child_image e+
     match e with DoubleFour=>dsize|_=>asize end)
}.

Definition pre e (w t:buffer) := match e with
 | DoubleFour=>loose_xyz w
 | Cached _ a row=>cached_point_bounds w /\ cache_bounds a (slice t row) /\
   (row+footprint e<=55)%nat
 | Ladder _=>loose_xyz w /\ cache_bounds false (slice t 0) /\
   cache_bounds true (slice t 20) /\ cache_bounds false (slice t 35)
 | _=>False end.
Definition post e (w t v:buffer) := match e with
 | DoubleFour=>double_spec defer_double w v
 | Cached f a row=>addition_spec (defer_add f a) f a w (slice t row) v
 | Ladder f=>ladder_post f w t v
 | _=>False end.

Definition result_mode e := match e with DoubleFour=>defer_double|Cached f a _=>defer_add f a|_=>false end.
Lemma post_bounds e w t v : pre e w t -> post e w t v ->point_bounds (result_mode e) v.
Proof.
 destruct e;try contradiction.
 - intros B D c j C J;apply (proj1(D B j c J C)).
 - intros [B [C _]] [_ D] i j I J;apply (proj1(D (conj B C) j i J I)).
 - intros _ [B _];exact B.
Qed.

(* Convert the native return into the exact operand view used by the
   caller. Caller-saved registers, vector registers and flags are arbitrary. *)
Theorem child_correct slide pt base e rs vs flags m :
 let w:=buffer_words m pt in let t:=buffer_words m base in
 let entry:=CPU (child_regs pt base e rs) vs flags m in
 arena slide pt base -> well_formed entry ->
 read_word m (base-8)=slide+continuation e -> pre e w t ->
 exists out,child_run slide base e entry (slide+continuation e) out /\
 post e w t (buffer_words (mem out) pt) /\
 (forall ip other,child_run slide base e entry ip other -> ip=slide+continuation e /\ other=out).
Proof.
 intros w t entry [Place Direct] WF Ret P.
 pose proof Place as Layout.
 destruct Layout as [Pad SA PA CA SF PF CF PS CS CP Code].
 assert (End:WordBounds.word64(base-8+8)) by (unfold fits64,WordBounds.word64 in *;lia).
 assert (Unique: L.double4_pc<>L.cached_pc) by (vm_compute;discriminate).
 Local Ltac geometry := unfold fits64,disjoint,WordBounds.word64 in *;lia.
 assert (FU: functional (dispatch (slide+L.double4_pc) (slide+L.cached_pc) (base-1344) 48)) by (apply dispatch_unique;lia).
 Local Ltac finish_direct FU R := split;[exact R|];split;[|intros ip other H;
   exact (FU _ _ _ _ _ _ H R)].
 destruct e as [n| | |f a row|f];try contradiction.
 - destruct(Direct DoubleFour ltac:(auto)) as [RW Away].
   destruct(Code _ _ (or_intror(or_introl eq_refl))) as [Fits [PD [_ SD]]].
   assert (Loc:Double4Memory.valid_placement (call_loc (base-1344) (slide+L.double4_pc) entry) dsize 48).
   { unfold Double4Memory.valid_placement,PointFrame.point_placement,call_loc,layout_at;
     cbn [origin code_base caller_pc PointFrame.point PointFrame.scratch].
     change (regs entry 7%nat) with pt;change (regs entry 4%nat) with (base-8);change (mem entry) with m.
     rewrite Ret;repeat apply conj;try assumption;try geometry;cbv [PointFrame.permitted_padding In];auto. }
   destruct(mode_double_call (slide+L.double4_pc) (slide+L.cached_pc) (base-1344) 48 entry WF
    ltac:(change (base-8=base-1344+1288+48);lia) End Loc) as [out [R [_ Spec]]].
   change (caller_pc(call_loc _ _ entry)) with (read_word m (base-8)) in R;rewrite Ret in R.
   exists out;finish_direct FU R;exact Spec.
 - destruct P as [B [C Len]].
   destruct(Direct (Cached f a row) ltac:(right;eauto)) as [RW Away].
   destruct(Code _ _ (or_intror(or_intror(or_introl eq_refl)))) as [Fits [PD [CD SD]]].
   assert (Size:64*Z.of_nat row+CachedAddABI.cache_length a<=3520)
     by (destruct a;cbn [footprint CachedAddABI.cache_length] in *;lia).
   assert (Al:(base+64*Z.of_nat row) mod 64=0) by
    (rewrite Z.mul_comm,Z.mod_add by lia;exact CA).
   assert (SP0:regs entry 4%nat=base-8) by (unfold entry,child_regs;destruct(defer_add f a);reflexivity).
   assert (Loc:CachedAddMemory.valid_placement a (call_loc (base-1344) (slide+L.cached_pc) entry) asize 48).
   { unfold CachedAddMemory.valid_placement,PointFrame.point_placement,call_loc,layout_at;
     cbn [origin code_base caller_pc PointFrame.point PointFrame.scratch CachedAddABI.cached].
     assert (Ptr:regs entry 7%nat=pt) by (unfold entry,child_regs;destruct(defer_add f a);reflexivity).
     rewrite Ptr.
     assert (Pointer:regs entry 6%nat=base+64*Z.of_nat row) by (unfold entry,child_regs;destruct (defer_add f a);reflexivity).
     rewrite Pointer,SP0;change (mem entry) with m.
     rewrite Ret;repeat apply conj;try assumption;try geometry;cbv [PointFrame.permitted_padding In];auto. }
   assert (D:slide+L.double4_pc<>add_target (slide+L.cached_pc) f a) by
     (unfold add_target;assert (N:L.double4_pc<>L.cached_pc+add_offset f a) by (destruct f,a;vm_compute;discriminate);lia).
   assert (Args:mode_args f a entry) by (unfold mode_args,entry,child_regs;destruct(defer_add f a);auto;split;reflexivity).
   destruct(mode_add_call (slide+L.double4_pc) (slide+L.cached_pc) (base-1344) 48 entry f a D WF
    ltac:(rewrite SP0;lia) ltac:(now rewrite SP0) Args Loc) as [out [R [_ Spec]]].
   change (caller_pc(call_loc _ _ entry)) with (read_word m (regs entry 4%nat)) in R;rewrite SP0,Ret in R.
   replace (add_target (slide+L.cached_pc) f a) with (slide+child_pc (Cached f a row)) in R by (unfold child_pc,add_target;ring).
   assert (Pt:regs entry 7%nat=pt) by (unfold entry,child_regs;destruct(defer_add f a);reflexivity).
   assert (Cache:regs entry 6%nat=base+64*Z.of_nat row) by (unfold entry,child_regs;destruct(defer_add f a);reflexivity).
   unfold point_words in Spec;rewrite Pt,Cache in Spec.
   exists out;finish_direct FU R;eapply addition_spec_ext;unfold agrees_words;[intros;reflexivity| |intros;reflexivity|exact Spec].
   intros;symmetry;apply offset_words.
 - destruct P as [B [O [Base E]]].
   assert (Cache:forall a row,cache_bounds a (slice t row) ->
     cache_bounds a (buffer_words m (base+64*Z.of_nat row))).
   { intros a row H i j I J;unfold cell;rewrite offset_words;apply H;assumption. }
   pose proof (Cache _ _ Base) as Base';pose proof (Cache _ _ E) as E'.
   destruct(LA.run_ladder LO.assembled_ladder_step_correct slide (base-1344) 16 pt base f entry Place WF
     ltac:(change (base-8=base-1344+1320+16);lia) eq_refl eq_refl eq_refl B O Base' E') as [out R].
   change (read_word (mem entry) (regs entry 4%nat)) with (read_word m (base-8)) in R;rewrite Ret in R.
   exists out;split;[exact(LA.returned R)|];split;[|apply (LA.unique_return _ _ _ _ _ _ _ _ _ R)].
   destruct R as [_ _ _ _ _ Strict V Zero _];split;[exact Strict|];split;[|exact Zero].
   intros j J;specialize(V j J);unfold LA.result_value in V;unfold w,t;change (mem entry) with m in V.
   replace (cache_values true (slice (buffer_words m base) 20) j) with
     (cache_values true (buffer_words m (base+1280)) j) by (apply cache_values_ext;auto;intros;apply (offset_words m base 20)).
   replace (cache_values false (slice (buffer_words m base) 35) j) with
     (cache_values false (buffer_words m (base+2240)) j) by (apply cache_values_ext;auto;intros;apply (offset_words m base 35)).
   exact V.
Qed.
