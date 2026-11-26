From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.StoreHistory memory.ByteMemory memory.FlatMemory abi.SysV.
From Ed25519Simd Require Import Wide51 PointResults.
From Curve25519.group Require Import Affine Representation.
From Ed25519Simd.LadderStep Require History.
From Curve25519.group Require Import DoubleScalar.
From Ed25519Simd.FullLadder Require Import LinkedBytes Program Operands Execution Native Audit LoopFrame.
From Ed25519Simd.FullLadder Require LoopStageCall LoopStepCall LoopStage LoopReady RoundOperands.
Import ListNotations. Local Open Scope Z_scope.
Definition execute slide base p:=bind (LoopStepCall.enter slide p) (History.execute slide (base-1344) 16).
Record result slide s B A full n p q:Prop:=Result {
 next:ip q=slide+entry_pc+875; words:well_formed(machine q); stack:regs(machine q) 4%nat=base_of s;
 frame:intact slide s (machine q); count:regs(machine q) 15%nat=Z.of_nat n+1;
 history:StoreHistory.extends (writable s) p q;
 reduced:strict(LoopReady.point s q);
 value:extended (full && Nat.eqb n 0) (LoopReady.point s q) (accumulated s B A (32-n));
 omitted:(full && Nat.eqb n 0)=false ->zero_t(LoopReady.point s q)
}.
Lemma child_region s x:LA.writable (base_of s-1344) 16 (regs s 7%nat) x -> writable s x.
Proof. unfold LA.writable,writable,base_of,staging,pad_of,top;pose proof(Z.mod_pos_bound (regs s 4%nat) 64 ltac:(lia));lia. Qed.

Theorem checked slide s B A full n p:placement slide s -> valid_inputs (slide+stage_pc) (pad_of s) s ->
 valid_tables s B A -> regs s 9%nat=bits full -> well_formed(machine p) -> intact slide s (machine p) ->
 ip p=slide+entry_pc+853 -> regs(machine p) 4%nat=base_of s -> regs(machine p) 15%nat=Z.of_nat n+1 ->
 (n<31)%nat -> LoopReady.loaded slide (mem(machine p)) -> RoundOperands.selected s (base_of s) n (mem(machine p)) ->
 strict(LoopReady.point s p) -> seeded_xyz (LoopReady.point s p) (accumulated s B A (32-S n)) ->
 exists q,execute slide (base_of s) p=Some q /\ result slide s B A full n p q.
Proof.
 intros P V T Mode WF F PC SP N Bound Map Rows Strict XYZ.
 destruct(LoopStepCall.checked _ _ _ _ _ P (proj1 V) WF F Mode PC SP N Bound (Map _ _ (or_introl eq_refl))) as [u [Call E]].
 pose proof(LoopStepCall.writes _ _ _ _ _ _ E) as Push.
 pose proof(StoreHistory.lend _ _ _ _ (LoopStageCall.slot_work s) Push) as Paid.
 pose proof(LoopReady.after _ _ _ _ P Map Paid) as Code.
 pose proof(StoreHistory.lend (LoopStageCall.slot s) (LoopStage.band s) _ _ ltac:(unfold LoopStageCall.slot,LoopStage.band;intros;lia) Push) as Narrow.
 pose proof(LoopReady.point_kept _ _ _ _ P Narrow) as Same.
 assert (Selected:RoundOperands.selected s (base_of s) n (mem(machine u))).
 { apply (RoundOperands.stable _ _ _ _ _ Rows);intros x X;apply (StoreHistory.preserves _ _ _ Push);unfold LoopStageCall.slot;lia. }
 pose proof(RoundOperands.checked _ _ _ _ n _ S.Odd B A V T ltac:(lia) Selected) as [OB Odd].
 pose proof(RoundOperands.checked _ _ _ _ n _ S.Base B A V T ltac:(lia) Selected) as [BB Base].
 pose proof(RoundOperands.checked _ _ _ _ n _ S.Even B A V T ltac:(lia) Selected) as [EB Even].
 unfold RoundOperands.cache in OB,Odd,BB,Base,EB,Even;cbn [affine SA.first_row Z.of_nat] in OB,Odd,BB,Base,EB,Even.
 change (64*Z.of_nat(SA.first_row S.Odd)) with 0 in OB,Odd;rewrite Z.add_0_r in OB,Odd.
 destruct(LoopStepCall.parameters _ _ _ _ _ _ E) as [US [Pt [Cache Flag]]].
 assert (UStack:regs(machine u) 4%nat=base_of s-1344+1320+16) by lia.
 destruct(History.checked slide (base_of s-1344) 16 (regs s 7%nat) (base_of s) (full && Nat.eqb n 0) u
   (LoopStepCall.address _ _ _ _ _ _ E) (LoopReady.step_images _ _ Code) (ladder_placement _ _ _ (child_layout _ _ P))
   (LoopStepCall.words _ _ _ _ _ _ E) UStack Pt Cache Flag (strict_loose _ (LoopReady.strict_kept _ _ Same Strict)) OB BB EB) as [q [Run End]].
 pose proof(History.writes _ _ _ _ _ _ _ End) as Child;pose proof(StoreHistory.lend _ _ _ _ (child_region s) Child) as Done.
 pose proof(StoreHistory.compose _ _ _ _ Paid Done) as Hist.
 assert (G:forall g,In g sysv_saved -> regs(machine q) g=regs(machine p) g).
 { intros g I;rewrite (History.saved _ _ _ _ _ _ _ End) by exact I;apply (LoopStepCall.saved _ _ _ _ _ _ E),I. }
 exists q;split;[unfold execute;now rewrite Call|constructor].
 - rewrite (History.back _ _ _ _ _ _ _ End),US;exact (LoopStepCall.link _ _ _ _ _ _ E).
 - exact (History.words _ _ _ _ _ _ _ End).
 - rewrite (History.stack _ _ _ _ _ _ _ End),US;ring.
 - eapply LoopFrame.after;[exact P|exact F|intros r I;apply G;cbv [live In] in I;cbv [sysv_saved In];tauto|exact Hist].
 - rewrite G by (cbv [sysv_saved In];tauto);exact N.
 - exact Hist.
 - exact (History.bound _ _ _ _ _ _ _ End).
 - intros j J;pose proof(History.value _ _ _ _ _ _ _ End j (accumulated s B A (32-S n) j) (operand_point s B A j n S.Odd) (operand_point s B A j n S.Base) (operand_point s B A j n S.Even) J
     ltac:(change (represents_xyz (point_values (LoopReady.point s u) j) (accumulated s B A (32-S n) j));rewrite (point_values_ext _ _ _ Same J);apply XYZ,J)
     (Odd j J) (Base j J) (Even j J)) as R.
   unfold operand_point,weight,affine in R;cbn iota in R;unfold accumulated in R |- *.
   rewrite digit_ladder_round in R by lia; exact R.
 - exact (History.omitted _ _ _ _ _ _ _ End).
Qed.
