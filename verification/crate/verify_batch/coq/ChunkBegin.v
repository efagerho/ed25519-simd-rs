From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds execution.ScalarBytes
 execution.ScalarWords execution.MappedFetch memory.MemoryGeometry.
From Ed25519Simd.VerifyBatch Require Import Policy Image Return StageEntry.
From Ed25519Simd.VerifyBatch Require Iteration ChunkRows ChunkStaging BatchWindow.
Local Open Scope Z_scope.

Theorem checked o text delta e cf :placement e -> ChunkRows.readable e ->
 physical o text delta e -> exists p,Iteration.begin o text e cf=Some p /\ ChunkStaging.entry o delta e 0 (Scatter.count e) p.
Proof.
 intros P Read Start.
 destruct(Start cf) as [n [_ [Budget [last [ws [Run [[ABI [Matrix [Meta [Saved [[Id [Scratch Tables]] [Cursor _]]]]]] [Replay Prefix]]]]]]]].
 destruct(Prefix n ltac:(lia)) as [mid [w [R Safe]]];rewrite Run in R;injection R as <- <-.
 set(p:=LinkedRun.finish o (LinkedRun.initial o e cf) (last,ws)).
 destruct ABI as [Dest [SP [Ret [SI [CX [DI [Output Left]]]]]]].
 exists p;split;[unfold Iteration.begin,StageEntry.observe;rewrite Budget,Run;reflexivity|constructor].
 - change (absolute o last=word(o+delta));unfold absolute;rewrite Dest;ring.
 - split;[exact Safe|intro x;unfold p;cbn [LinkedRun.finish log machine LinkedRun.initial];now rewrite Replay].
 - exact (mapped_run_wf _ _ _ (State (Running 0) e cf) _ _ (initial_cpu _ P) Run).
 - exact SP.
 - exact Ret.
 - exact Matrix.
 - exact Meta.
 - exact (conj SI (conj CX (conj DI Id))).
 - exact (conj Scratch Output).
 - exact (eq_trans Left (@BatchWindow.live_count BatchWindow.initial e (initial_cpu _ P))).
 - intro More;change (regs(cpu_state last) 3%nat=ChunkRows.base e 8);rewrite (Cursor More).
   destruct Read as [[L H] _];apply word_fits;unfold word64,ChunkRows.base in *;lia.
 - exact Saved.
 - exact Tables.
Qed.
