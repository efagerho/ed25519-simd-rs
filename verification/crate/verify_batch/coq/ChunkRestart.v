From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds execution.WordSemantics
 execution.ScalarBytes execution.MappedFetch memory.MemoryGeometry memory.FlatMemory.
From Ed25519Simd.VerifyBatch Require Import Image Return StageEntry RejectExecution.
From Ed25519Simd.VerifyBatch Require ChunkRows ChunkStaging.
Local Open Scope Z_scope.

Definition code text delta := StageEntry.bound text /\ TailWrites.bound text /\
 StageWrites.bound text delta /\ ChunkStaging.preserves_bp text=true.

(* The back edge leaves R13 at the original output capacity. Only R12 and
   the descriptor pointer advance when the next eight rows are staged. *)
Theorem checked o text delta e p values : code text delta -> placement e -> ChunkRows.readable e ->
 mapped (mem e) o text -> (forall x,o<=x<o+Z.of_nat(length text) -> ~writable e x) ->
 post_with values o e (NextChunk p) ->
 exists q,ChunkStaging.execute o text (Scatter.count e-8) p=Some q /\
   ChunkStaging.entry o delta e 8 (Scatter.count e-8) q.
Proof.
 intros [Select [Tail [Transfer BP]]] P Read Map Sep
    [Paid [_ [_ [More [PC [SP [Remaining [_ [Saved [Bindings W]]]]]]]]]].
 destruct Bindings as [Globals Cursor Tables].
 apply ChunkStaging.checked;try assumption;try lia.
 - exact (conj SP Globals).
 - rewrite (Cursor More);change (word(regs e 7%nat+320)=regs e 7%nat+320).
   destruct Read as [[L H] _];apply word_fits;unfold word64 in *;lia.
Qed.
