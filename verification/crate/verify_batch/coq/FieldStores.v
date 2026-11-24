From Coq Require Import ZArith List Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch execution.InstructionRoute
 execution.ScalarBytes execution.ScalarWords execution.AlignedRows memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare.
Local Open Scope Z_scope.

Record result sig bias e pc delta p q : Prop:=Result {
 at_next:ip q=base bias+AlignedRows.after true pc 0 7 delta 5;
 logged:accounted e (writable e) q;
 words:well_formed(machine q);
 gprs:regs(machine q)=regs(machine p);
 zmm:vectors(machine q)=vectors(machine p);
 stored:AlignedRows.saved (machine p) (machine q) (point e sig+delta) 0 5;
 outside:preserved (fun x=>~(point e sig+delta<=x<point e sig+delta+320)) (mem(machine p)) (mem(machine q))
}.

Theorem execute sig pol bias e pc delta p :
 placement e -> loaded pol bias (mem e) (writable e) ->
 linked text (AlignedRows.route true pc 0 7 delta 5) -> 0<=delta<=960 -> delta mod 64=0 ->
 ip p=base bias+pc -> accounted e (writable e) p -> well_formed(machine p) -> regs(machine p) 7%nat=point e sig ->
 exists q,segment (base bias) text 5 p=Some q /\ result sig bias e pc delta p q.
Proof.
 intros P I Route D Al PC Acc W DI;set (a:=point e sig) in *.
 destruct(scratch_ok _ P) as [[Lo Hi] Align];assert (A:a mod 64=0) by (apply point_aligned,Align).
 destruct(AlignedRows.stores (base bias) _ 5 pc 0 7 delta (a+delta) (machine p) (LinkedRun.carry p)
   Route ltac:(now rewrite DI) ltac:(rewrite Z.add_mod,A,Al by lia;reflexivity)
   ltac:(unfold fits64,a,point,point_offset;destruct sig;change (Z.of_nat 5) with 5;lia)
   ltac:(intros i j N J;exact (proj1(proj2 W) j i J))) as [v [ws [Run [G [V [_ [Safe Rows]]]]]]].
 assert (Allowed:confined (writable e) ws).
 { apply Forall_impl with (P:=permits (range (a+delta) 5));[|exact Safe].
   intros w H x X;specialize(H x X);right;left;unfold span,range,a,point,point_offset in *;destruct sig;change (Z.of_nat 5) with 5 in H;lia. }
 destruct(mapped_now _ _ _ I _ _ _ Acc (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ _ _ text 5 pc _ _ Acc PC Map Sep Run Allowed) as [Next Paid].
 eexists;split;[exact Next|constructor];[reflexivity|exact Paid|exact (segment_wf _ _ _ _ _ W Next)|exact G|exact V|exact Rows|].
 pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Run)) as M;change (mem v=WriteTrace.replay (mem(machine p)) ws) in M.
 intros x X;change (mem v x=mem(machine p) x);rewrite M;apply (WriteTrace.frame _ _ Safe),X.
Qed.
