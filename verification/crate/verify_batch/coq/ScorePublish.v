From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 execution.MappedFetch memory.ByteMemory memory.FlatMemory memory.WriteTrace memory.MemoryGeometry abi.SysV.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require ScoreContinue ScoredZero StrictDispatch.
Local Open Scope Z_scope.

Definition scatter bias pc text p:=bind (Scattered.execute bias p) (ScoreContinue.execute (bias+pc) text).
Definition execute bias pc text p:=bind (ScoredZero.execute bias p) (scatter bias pc text).

Definition stored e p mask (m:FlatMemory.bytes):=forall j,(j<Nat.min (Scatter.count e) 8)%nat ->
 m(output e+Z.of_nat(Scatter.position e j))=ScatterValues.verdict
   (fun i=>mem(machine p)(Rows.frame e+856+Z.of_nat i)) mask j.

Lemma publish_values mask pol bias pc dst text e t p : Image.matches pc dst text -> StrictDispatch.bound pc text ->
 placement e -> loaded pol bias (mem e) (writable e) -> fits64 (bias+pc) (Z.of_nat(length text)) ->
 mapped (mem e) (bias+pc) text -> (forall x,bias+pc<=x<bias+pc+Z.of_nat(length text) -> ~writable e x) ->
 (0<Scatter.count e)%nat -> Scatter.indices e -> ScoreTail.entry bias pc e t p mask ->
 exists r,scatter bias pc text p=Some r /\ RejectExecution.post_with (stored e p mask) (bias+pc) e r.
Proof.
 intros Code [_ [_ [Exit Len]]] P I Range Map Sep Live Idx Tail.
 destruct(ScoreTail.args _ _ _ _ _ _ Tail) as [AX [DI [SI DX]]].
 assert (N:regs(machine p) 2%nat=Z.of_nat(Scatter.count e)).
 { rewrite DX;unfold Scatter.count;rewrite Z2Nat.id by apply (initial_cpu _ P);reflexivity. }
 pose proof(ScoreTail.target _ _ _ _ _ _ Tail) as PC;pose proof(ScoreTail.writes _ _ _ _ _ _ Tail) as Paid.
 destruct(Scattered.checked pol bias e p _ P I Paid PC (ScoreTail.sp _ _ _ _ _ _ Tail)
    (ScoreTail.ret _ _ _ _ _ _ Tail) SI N (proj2(proj2(ScoreTail.words _ _ _ _ _ _ Tail)))) as [q [Run End]].
 destruct(mapped_now _ _ _ I _ _ _ Paid (LoadedImage.scatter pol)) as [Child Apart].
 assert (O:regs(machine q) 0%nat=1 /\ stored e p mask (mem(machine q))).
 { eapply RejectOutputs.published_values;[exact P|exact Live|exact Idx|exact PC|exact DI|exact SI|exact N|exact AX|
     exact (ScoreTail.metadata _ _ _ _ _ _ Tail)|exact Child| |exact Run].
   intros x X Y;apply (Apart x X);right;right;exact Y. }
 assert (Back:ip q=bias+pc+539).
 { rewrite (Scattered.target _ _ _ _ End);apply word_fits;change (574<Z.of_nat(length text)) in Len;unfold fits64,word64 in *;lia. }
 assert (Left:regs(machine q) 12%nat=Prologue.rows_left (regs e 6%nat)).
 { rewrite (Scattered.saved _ _ _ _ End) by (simpl;tauto);exact (ScoreTail.left _ _ _ _ _ _ Tail). }
 destruct(ScoreTail.saved _ _ _ _ _ _ Tail) as [Spills BP].
 assert (Saved:StageEntry.saved_caller e (machine q)).
 { split.
   - intros x X;rewrite (Scattered.outside _ _ _ _ End) by
       (destruct(out_stack _ P);unfold Scattered.region,FlatMemory.disjoint in *;lia);apply Spills,X.
   - rewrite (Scattered.saved _ _ _ _ End) by (simpl;tauto);exact BP. }
 destruct(ScoreContinue.checked_with (stored e p mask) _ _ _ _ _ _ Code Exit P Map Sep Back (Scattered.stack _ _ _ _ End)
   (Scattered.writes _ _ _ _ End) Left Saved O (Scattered.bytes _ _ _ _ End)) as [r [Next Post]].
 exists r;split;[unfold scatter;rewrite Run;exact Next|exact Post].
Qed.
Lemma publish pol bias pc dst text e t p : Image.matches pc dst text -> StrictDispatch.bound pc text ->
 placement e -> loaded pol bias (mem e) (writable e) -> fits64 (bias+pc) (Z.of_nat(length text)) ->
 mapped (mem e) (bias+pc) text -> (forall x,bias+pc<=x<bias+pc+Z.of_nat(length text) -> ~writable e x) ->
 (0<Scatter.count e)%nat -> Scatter.indices e -> ScoreTail.entry bias pc e t p 0 ->
 exists r,scatter bias pc text p=Some r /\ RejectExecution.post (bias+pc) e r.
Proof.
 intros Code Bound P I Range Map Sep Live Idx Tail.
 destruct(publish_values 0 _ _ _ _ _ _ _ _ Code Bound P I Range Map Sep Live Idx Tail) as [r [Run Done]].
 exists r;split;[exact Run|eapply RejectExecution.post_map;[|exact Done]].
 intros m Values j J;rewrite (Values _ J);apply ScatterZeros.rejected.
Qed.

Theorem checked bias pc dst text e caller stop : Image.matches pc dst text -> StrictDispatch.bound pc text ->
 placement e -> loaded Dalek bias (mem e) (writable e) -> fits64 (bias+pc) (Z.of_nat(length text)) ->
 mapped (mem e) (bias+pc) text -> (forall x,bias+pc<=x<bias+pc+Z.of_nat(length text) -> ~writable e x) ->
 (0<Scatter.count e)%nat -> Scatter.indices e -> StrictScreen.decision bias e stop ->
 StrictScoreFrame.context bias pc e caller stop -> regs(machine stop) 12%nat=0 ->
 exists r,execute bias pc text stop=Some r /\ RejectExecution.post (bias+pc) e r.
Proof.
 intros Code Bound P I Range Map Sep N Idx D F Zero.
 destruct(ScoredZero.checked _ _ _ _ _ P I D F Zero) as [p [Prepare [t [_ Tail]]]].
 destruct(publish _ _ _ _ _ _ _ _ Code Bound P I Range Map Sep N Idx Tail) as [r [Run Post]].
 exists r;split;[unfold execute;rewrite Prepare;exact Run|exact Post].
Qed.
