From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.StoreHistory memory.ByteMemory abi.SysV.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.FullLadder Require Import LinkedBytes Operands Native Execution Audit LoopFrame.
From Ed25519Simd.FullLadder Require LoopReady LoopControl LoopStage LoopStep.
Import ListNotations. Local Open Scope Z_scope.
Definition iteration slide base p:=bind (LoopStage.execute slide p) (fun staged=>
 bind (LoopStep.execute slide base staged) (LoopControl.advance slide)).
Fixpoint execute slide base n p:=match n with O=>Some p | S m=>
 bind (iteration slide base p) (execute slide base m) end.

Section Rounds.
Variables (slide:Z) (s:cpu) (B:Affine.point) (A:nat->Affine.point) (full:bool).
Hypothesis P:placement slide s.
Hypothesis V:valid_inputs (slide+stage_pc) (pad_of s) s.
Hypothesis T:valid_tables s B A.
Hypothesis Flag:regs s 9%nat=bits full.
Record boundary count p:Prop:=Boundary {
 at_body:ip p=slide+entry_pc+828; words:well_formed(machine p); stack:regs(machine p) 4%nat=base_of s;
 counter:regs(machine p) 15%nat=Z.of_nat count; frame:intact slide s (machine p);
 mapped:LoopReady.loaded slide (mem(machine p)); bound:strict(LoopReady.point s p);
 point:seeded_xyz (LoopReady.point s p) (accumulated s B A (32-count))
}.
Record result p q:Prop:=Result {
 next:ip q=slide+entry_pc+880; wf:well_formed(machine q); intact_frame:intact slide s (machine q);
 history:StoreHistory.extends (writable s) p q; final_bound:strict(LoopReady.point s q);
 value:extended full (LoopReady.point s q) (accumulated s B A 32);
 omitted:full=false ->zero_t(LoopReady.point s q)
}.
Lemma checked n : forall p,boundary (S n) p -> (n<31)%nat ->
 exists q,execute slide (base_of s) (S n) p=Some q /\ result p q.
Proof.
 induction n as [|n IH]. all: intros p F N.
 all: destruct F as [PC W SP Count F Code Strict XYZ];rewrite Nat2Z.inj_succ in Count;
   match type of Count with _=Z.succ ?v=>change (Z.succ v) with (v+1) in Count end.
 all: destruct(LoopStage.checked _ _ _ _ P V W F PC SP Count N (Code _ _ (or_introl eq_refl))
    (Code _ _ (or_intror(or_introl eq_refl)))) as [a [Stage SA]].
 all: pose proof(LoopStage.writes _ _ _ _ _ SA) as SH;
   pose proof(StoreHistory.lend _ _ _ _ (LoopStage.work s) SH) as Paid;
   pose proof(LoopReady.after _ _ _ _ P Code Paid) as Ac;
   pose proof(LoopReady.point_kept _ _ _ _ P SH) as Same.
 all: assert (AN:regs(machine a) 15%nat=regs(machine p) 15%nat) by
   (apply (LoopStage.saved _ _ _ _ _ SA);cbv [sysv_saved In];tauto).
 all: destruct(LoopStep.checked _ _ _ _ _ _ _ P V T Flag (LoopStage.words _ _ _ _ _ SA)
    (LoopStage.frame _ _ _ _ _ SA) (LoopStage.next _ _ _ _ _ SA) (LoopStage.stack _ _ _ _ _ SA)
    (eq_trans AN Count) N Ac (LoopStage.rows _ _ _ _ _ SA) (LoopReady.strict_kept _ _ Same Strict)
    ltac:(intros j J;rewrite (point_values_ext _ _ _ Same J);apply XYZ,J)) as [b [Step SB]].
 all: pose proof(LoopStep.history _ _ _ _ _ _ _ _ SB) as BH;
   pose proof(StoreHistory.compose _ _ _ _ Paid BH) as Prev;
   pose proof(LoopReady.after _ _ _ _ P Code Prev) as Bc;
   destruct(LoopControl.advance_checked _ _ _ (LoopStep.next _ _ _ _ _ _ _ _ SB)
    (LoopStep.words _ _ _ _ _ _ _ _ SB) (LoopStep.count _ _ _ _ _ _ _ _ SB) N
    (Bc _ _ (or_introl eq_refl))) as [c [Branch C]];
   pose proof(StoreHistory.compose _ _ _ _ Prev (LoopControl.history _ _ _ _ _ C)) as Hist;
   pose proof(LoopControl.intact_after _ _ _ _ _ _ (LoopStep.frame _ _ _ _ _ _ _ _ SB) C) as CF;
   pose proof(LoopStep.value _ _ _ _ _ _ _ _ SB) as BV;
   pose proof(LoopStep.reduced _ _ _ _ _ _ _ _ SB) as Bounds;
   pose proof(LoopControl.memory _ _ _ _ C) as Mem.
 - exists c;split.
   + cbn [execute];unfold iteration;rewrite Stage;cbn [bind];rewrite Step;cbn [bind];now rewrite Branch.
   + constructor;[exact (LoopControl.next _ _ _ _ C)|exact (LoopControl.words _ _ _ _ C)|exact CF|exact Hist| | |].
     * unfold LoopReady.point in *;now rewrite Mem.
     * change (extended (full && true) (LoopReady.point s b) (accumulated s B A 32)) in BV;rewrite Bool.andb_true_r in BV;unfold LoopReady.point in *;now rewrite Mem.
     * pose proof(LoopStep.omitted _ _ _ _ _ _ _ _ SB) as O;change (full && true=false ->zero_t(LoopReady.point s b)) in O.
       rewrite Bool.andb_true_r in O;unfold LoopReady.point in *;now rewrite Mem.
 - assert (Next:boundary (S n) c).
   { constructor;[exact (LoopControl.next _ _ _ _ C)|exact (LoopControl.words _ _ _ _ C)| |exact (LoopControl.counter _ _ _ _ C)|exact CF| | |].
     - rewrite (LoopControl.same _ _ _ _ C) by discriminate;apply (LoopStep.stack _ _ _ _ _ _ _ _ SB).
     - exact (LoopReady.after _ _ _ _ P Code Hist).
     - unfold LoopReady.point in *;now rewrite Mem.
     - intros j J;unfold LoopReady.point in *;rewrite Mem;exact (proj1(BV j J)). }
   destruct(IH c Next ltac:(lia)) as [q [Tail End]];exists q;split.
   + change (bind (iteration slide (base_of s) p) (execute slide (base_of s) (S n))=Some q).
     unfold iteration;rewrite Stage;cbn [bind];rewrite Step;cbn [bind];now rewrite Branch.
   + destruct End as [At WF QF TailH QB PV O];constructor;try assumption;exact (StoreHistory.compose _ _ _ _ Hist TailH).
Qed.
End Rounds.
