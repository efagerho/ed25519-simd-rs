From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds execution.WordSemantics
 execution.ScalarBytes execution.MappedFetch memory.MemoryGeometry memory.FlatMemory.
From Ed25519Simd.VerifyBatch Require Import Image Return StageEntry RejectExecution.
From Ed25519Simd.VerifyBatch Require ChunkRows ChunkStaging BatchWindow.
Local Open Scope Z_scope.

Definition code text delta := StageEntry.bound text /\ TailWrites.bound text /\
 StageWrites.bound text delta /\ ChunkStaging.preserves_bp text=true.

(* The back edge leaves R13 at the original output capacity. Only R12 and
   the descriptor pointer advance when the next eight rows are staged. *)
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem checked o text delta e p values : code text delta -> placement e -> ChunkRows.readable e ->
 mapped (mem e) o text -> (forall x,o<=x<o+Z.of_nat(length text) -> ~writable e x) ->
 post_with values o e (NextChunk p) ->
 exists q,ChunkStaging.execute o text (BatchWindow.remaining e-8) p=Some q /\
   ChunkStaging.entry o delta e (BatchWindow.first+8) (BatchWindow.remaining e-8) q.
Proof.
 intros [Select [Tail [Transfer BP]]] P Read Map Sep
    [Paid [_ [_ [More [PC [SP [Remaining [_ [Saved [Bindings W]]]]]]]]]].
 destruct Bindings as [Globals Cursor Tables].
 pose proof (BatchWindow.total e ltac:(lia)) as Total.
 apply ChunkStaging.checked;try assumption;try lia.
 - exact (conj SP Globals).
 - rewrite (Cursor More);unfold ChunkRows.base;rewrite Nat2Z.inj_add.
   destruct Read as [[L H] _];rewrite word_fits by (unfold word64 in *;lia);ring.
Qed.
End Iteration.
