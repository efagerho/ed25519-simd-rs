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
Definition child_pc e := match e with DoubleFour=>L.double4_pc | Cached _ _ _=>L.cached_pc
 | Ladder _=>L.wrapper_pc | _=>LinkedBytes.stage_pc end.
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
 | Cached f a row=>Instructions.put (Instructions.put (Instructions.put rs 6
    (base+64*Z.of_nat row)) 2 (bits f)) 1 (bits a)
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
   ~(slide+child_pc e<=slide+continuation e<slide+child_pc e+
     match e with DoubleFour=>dsize|_=>asize end)
}.

Definition pre e (w t:buffer) := match e with
 | DoubleFour=>loose_xyz w
 | Cached _ a row=>strict w /\ cache_bounds a (slice t row) /\
   (row+footprint e<=55)%nat
 | Ladder _=>loose_xyz w /\ cache_bounds false (slice t 0) /\
   cache_bounds true (slice t 20) /\ cache_bounds false (slice t 35)
 | _=>False end.
Definition post e (w t v:buffer) := match e with
 | DoubleFour=>Double4Spec.double4_spec w v
 | Cached f a row=>CachedAddSpec.cached_add_spec f a w (slice t row) v
 | Ladder f=>ladder_post f w t v
 | _=>False end.

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
   destruct(double_call (slide+L.double4_pc) (slide+L.cached_pc) (base-1344) 48 entry WF
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
   assert (Loc:CachedAddMemory.valid_placement a (call_loc (base-1344) (slide+L.cached_pc) entry) asize 48).
   { unfold CachedAddMemory.valid_placement,PointFrame.point_placement,call_loc,layout_at;
     cbn [origin code_base caller_pc PointFrame.point PointFrame.scratch CachedAddABI.cached].
     change (regs entry 7%nat) with pt;change (regs entry 4%nat) with (base-8);
     change (regs entry 6%nat) with (base+64*Z.of_nat row);change (mem entry) with m.
     rewrite Ret;repeat apply conj;try assumption;try geometry;cbv [PointFrame.permitted_padding In];auto. }
   destruct(add_call (slide+L.double4_pc) (slide+L.cached_pc) (base-1344) 48 entry f a WF
    ltac:(change (base-8=base-1344+1288+48);lia) End eq_refl eq_refl Loc) as [out [R [_ Spec]]].
   change (caller_pc(call_loc _ _ entry)) with (read_word m (base-8)) in R;rewrite Ret in R.
   exists out;finish_direct FU R;eapply CachedAddSpec.spec_ext;[intros;reflexivity| |intros;reflexivity|exact Spec].
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
