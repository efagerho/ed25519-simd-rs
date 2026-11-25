From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch execution.WordBounds
 memory.MemoryGeometry memory.FlatMemory memory.WriteTrace abi.RunCalls.
From Ed25519Simd.LadderStep Require Import LinkedBytes Callees Audit Calls.
From Ed25519Simd.LadderStep Require PointTrace.
Import ListNotations. Local Open Scope Z_scope.

Definition images slide m:=mapped m (slide+wrapper_pc) symbol_bytes /\
 mapped m (slide+double4_pc) doubling_image /\ mapped m (slide+cached_pc) addition_image.
Definition outcome_of (q:cursor):RunCalls.outcome:=(ip q,machine q,log q).
Definition leaf slide sc pad a s :=
 let p:=initial a s None in
 option_map outcome_of
 (if a=?slide+double4_pc then PointTrace.double (slide+double4_pc) sc pad p
  else if a=?slide+cached_pc then PointTrace.add (slide+cached_pc) sc pad
     (regs s 2%nat=?1) (regs s 1%nat=?1) p else None).

Lemma keep slide sc pad pt cache: placement_ok slide sc pad pt cache ->
 forall m ws,images slide m -> confined (writable sc pad pt) ws -> images slide (replay m ws).
Proof.
 intros Place m ws [Code [D A]] W;unfold images;split;[|split];
 eapply keep_image;try eassumption;intros x X Hit.
 - destruct(code_regions _ _ _ _ _ Place _ _ (or_introl eq_refl)) as [_ [P [_ Stack]]];unfold writable,wrapper_size,disjoint in *;lia.
 - destruct(code_regions _ _ _ _ _ Place _ _ (or_intror(or_introl eq_refl))) as [_ [P [_ Stack]]].
   rewrite double_binding in X;unfold dsize in *;change (slide+double4_pc<=x<slide+double4_pc+Z.of_nat(length doubling_bytes)) in X;
   unfold doubling_bytes,writable,disjoint in *;lia.
 - destruct(code_regions _ _ _ _ _ Place _ _ (or_intror(or_intror(or_introl eq_refl)))) as [_ [P [_ Stack]]].
   rewrite add_binding in X;unfold asize in *;unfold addition_bytes,writable,disjoint in *;lia.
Qed.

Lemma slot slide sc pad pt a s ret out:0<=pad -> checked_call slide sc pad pt a s ret out ->
 forall x,regs s 4%nat<=x<regs s 4%nat+8 -> writable sc pad pt x.
Proof. intros Pad [_ [_ [SP _]]] x X;right;lia. Qed.

Lemma invoke slide sc pad pt a s ret out : 0<=pad -> checked_call slide sc pad pt a s ret out -> images slide (mem s) ->
 exists ws,leaf slide sc pad a s=Some(ret,out,ws) /\ confined (writable sc pad pt) ws /\
 mem out=replay (mem s) ws.
Proof.
 intros Pad [D [W [SP [End [Point [k [Addr Place]]]]]]] [_ [DoubleMap AddMap]].
 assert (Apart:slide+double4_pc<>slide+cached_pc) by (assert (double4_pc<>cached_pc) by (vm_compute;discriminate);lia).
 set(p:=initial a s None).
 assert (Return:forall q,PointTrace.result sc p q ->
    dispatch (slide+double4_pc) (slide+cached_pc) sc pad a s (ip q) (machine q) ->
    leaf slide sc pad a s=Some(outcome_of q) ->
    exists ws,leaf slide sc pad a s=Some(ret,out,ws) /\ confined (writable sc pad pt) ws /\ mem out=replay (mem s) ws).
 { intros q R Actual Run;destruct(dispatch_unique _ _ sc pad Apart _ _ _ _ _ _ D Actual) as [-> ->].
   destruct(PointTrace.writes _ _ _ R) as [ws [L [Safe M]]].
   exists ws;split;[rewrite Run;unfold outcome_of;now rewrite L|split;[|exact M]].
   eapply Forall_impl;[|exact Safe];intros w H x X;specialize(H x X);unfold callee_writable in H;change (machine p) with s in H.
   unfold writable;lia. }
 destruct k as [|f aff d].
 - change (a=slide+double4_pc) in Addr.
   destruct(PointTrace.double_run (slide+double4_pc) sc pad p Addr DoubleMap W SP End Place)
     as [q [Run [R [_ Actual]]]].
   apply (Return q R);[rewrite Addr;apply Actual|unfold leaf;fold p;rewrite Addr,Z.eqb_refl,Run;reflexivity].
 - destruct Place as [Flags Place].
   assert (FA:regs s 2%nat=CachedAddABI.flag_word f /\ regs s 1%nat=CachedAddABI.flag_word aff) by (destruct f,aff;exact Flags).
   destruct FA as [F A].
   assert (At:a=slide+cached_pc) by (destruct f,aff;change (a=slide+(cached_pc+0)) in Addr;lia).
   destruct(PointTrace.add_run (slide+cached_pc) sc pad f aff p At AddMap W SP End F A Place) as [q [Run [R [_ Actual]]]].
   apply (Return q R);[rewrite At;apply Actual|].
   unfold leaf;fold p;rewrite At,(proj2(Z.eqb_neq (slide+cached_pc) (slide+double4_pc)) ltac:(congruence)),Z.eqb_refl,F,A.
   assert (Bit:forall b,(CachedAddABI.flag_word b=?1)=b) by (destruct b;reflexivity).
   rewrite !Bit,Run;reflexivity.
Qed.
