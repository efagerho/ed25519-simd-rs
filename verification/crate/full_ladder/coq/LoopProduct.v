From Coq Require Import List ZArith Lia.
From ProofArithmetic Require Import Radix.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.StoreHistory memory.ByteMemory abi.SysV.
From Curve25519.group Require Import Affine Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.FullLadder Require Import LinkedBytes Operands ScalarAction Native Execution Audit LoopFrame.
From Ed25519Simd.FullLadder Require TopPair LoopReady LoopControl LoopRounds LoopReturn.
Local Open Scope Z_scope.
Definition execute slide p:=let base:=regs(machine p) 4%nat in bind (LoopControl.start slide p)
 (fun q=>bind (LoopRounds.execute slide base 31 q) (LoopReturn.execute slide)).
Record result s B A full p q:Prop:=Result {
 target:ip q=read_word (mem s) (top s); stack:regs(machine q) 4%nat=top s+8;
 saved:forall g,In g sysv_saved -> regs(machine q) g=regs s g; wf:well_formed(machine q);
 stores:StoreHistory.extends (writable s) p q; reduced:strict(LoopReady.point s q);
 value:extended full (LoopReady.point s q) (fun j=>combination (number 16 (digit_list s 1 j)) (number 16 (digit_list s 8 j)) B (A j));
 omitted:full=false ->zero_t(LoopReady.point s q)
}.
Theorem checked slide s B A full seed p:placement slide s -> valid_inputs (slide+stage_pc) (pad_of s) s -> valid_tables s B A ->
 regs s 9%nat=bits full -> intact slide s (machine p) -> LoopReady.loaded slide (mem(machine p)) ->
 TopPair.result slide s B A seed p -> exists q,execute slide p=Some q /\ result s B A full p q.
Proof.
 intros P V T Flag F Map Pair;pose proof(TopPair.resumed _ _ _ _ _ _ Pair) as Ready.
 destruct(LoopControl.start_checked _ _ (TopPair.next _ _ _ _ _ _ Pair) (TopPair.words _ _ _ Ready)
   (Map _ _ (or_introl eq_refl))) as [a [Start C]].
 pose proof(LoopControl.memory _ _ _ _ C) as M.
 assert (Boundary:LoopRounds.boundary slide s B A 31 a).
 { constructor;[exact (LoopControl.next _ _ _ _ C)|exact (LoopControl.words _ _ _ _ C)| |exact (LoopControl.counter _ _ _ _ C)| | | |].
   - rewrite (LoopControl.same _ _ _ _ C) by discriminate;exact (TopPair.stack _ _ _ Ready).
   - eapply LoopControl.intact_after;eassumption.
   - now rewrite M.
   - unfold LoopReady.point;rewrite M;apply (TopPair.reduced _ _ _ _ _ _ Pair).
   - unfold LoopReady.point;rewrite M;exact (TopPair.value _ _ _ _ _ _ Pair). }
 destruct(LoopRounds.checked _ _ _ _ _ P V T Flag 30%nat a Boundary ltac:(lia)) as [b [Rounds R]].
 pose proof(StoreHistory.compose _ _ _ _ (LoopControl.history _ _ _ _ _ C) (LoopRounds.history _ _ _ _ _ _ _ R)) as History.
 pose proof(LoopReady.after _ _ _ _ P Map History) as Code.
 destruct(LoopReturn.checked _ _ _ P (proj1 V) (LoopRounds.intact_frame _ _ _ _ _ _ _ R) (LoopRounds.wf _ _ _ _ _ _ _ R)
  (LoopRounds.next _ _ _ _ _ _ _ R) (Code _ _ (or_introl eq_refl))) as [q [Ret Done]].
 pose proof(LoopReturn.bytes _ _ _ Done) as End.
 exists q;split.
 - unfold execute;rewrite (TopPair.stack _ _ _ Ready),Start;cbn [bind];rewrite Rounds;exact Ret.
 - constructor;[exact (LoopReturn.back _ _ _ Done)|exact (LoopReturn.stack _ _ _ Done)|exact (LoopReturn.saved _ _ _ Done)|
   exact (LoopReturn.words _ _ _ Done)|exact (StoreHistory.compose _ _ _ _ History (LoopReturn.stores _ _ _ Done))| | |].
   + unfold LoopReady.point;rewrite End;apply (LoopRounds.final_bound _ _ _ _ _ _ _ R).
   + intros j J;pose proof(LoopRounds.value _ _ _ _ _ _ _ R j J) as Vj;unfold accumulated in Vj;rewrite !digits_number in Vj by lia.
     unfold LoopReady.point;rewrite End;exact Vj.
   + unfold LoopReady.point;rewrite End;exact (LoopRounds.omitted _ _ _ _ _ _ _ R).
Qed.
