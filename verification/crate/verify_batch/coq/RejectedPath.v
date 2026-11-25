From Coq Require Import List ZArith Lia.
From Machine Require Import execution.WordSemantics execution.LinkedCalls execution.LinkedRun execution.MappedFetch
 memory.ByteMemory memory.MemoryGeometry memory.FlatMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Image Return LoadedImage BatchScalar PrepareUnwind RejectExecution.
From Ed25519Simd.VerifyBatch Require RejectDispatch RejectFinish EligibilityFrame.
Local Open Scope Z_scope.

Definition execute decoded pol bias pc text p:=bind (unwind_at decoded pol bias p) (finish_chunk bias pc text).

Theorem checked decoded pol bias pc text e p :
 RejectDispatch.bound pc text -> RejectFinish.bound text -> placement e -> loaded pol bias (mem e) (writable e) ->
 fits64 (bias+pc) (Z.of_nat(length text)) -> offset Continue<Z.of_nat(length text) ->
 mapped (mem e) (bias+pc) text -> (forall x,bias+pc<=x<bias+pc+Z.of_nat(length text)->~writable e x) ->
 (0<Scatter.count e)%nat -> Scatter.indices e -> EligibilityFrame.context pol bias (bias+pc) e p ->
 accounted e (writable e) p -> byte_memory(mem(machine p)) -> regs(machine p) 4%nat=common_top pol e-104 ->
 ip p=bias+PrepareNative.common+unwind_offset decoded -> return_value decoded (machine p) mod 2^32=0 ->
 exists r,execute decoded pol bias pc text p=Some r /\ RejectExecution.post (bias+pc) e r.
Proof.
 intros ScatterCode ExitCode P I Range Len Map Apart N Idx [Links Outputs Meta [Slots BP] _] Acc Bytes SP Start Zero.
 destruct(rejected_at decoded pol bias (bias+pc) e p P I Start SP Acc Links Outputs Zero) as [q [Unwind Again]].
 destruct Again as [At [Stack [AX [Memory [Log [Args [Left Kept]]]]]]].
 assert (Paid:accounted e (writable e) q) by
   (split;[rewrite Log;apply Acc|intros x;rewrite Memory,Log;apply Acc]).
 destruct(finish_checked pol bias pc text e q ScatterCode ExitCode P I Range Len Map Apart N Idx Paid At Stack Args Left
    ltac:(now rewrite AX) ltac:(now rewrite Memory)
    ltac:(split;[now rewrite Memory|now rewrite Kept]) ltac:(now rewrite Memory))
   as [r [Finish Post]].
 exists r;split;[unfold execute;now rewrite Unwind|exact Post].
Qed.
