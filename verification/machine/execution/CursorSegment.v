From Coq Require Import List ZArith.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch execution.ScalarBytes
 execution.ScalarWords execution.WordBounds memory.WriteTrace.
From Machine Require execution.StoreHistory.
Local Open Scope Z_scope.

Definition valid_cursor entry allowed p :=
 accounted entry allowed p /\ well_formed (machine p).

Theorem checked e allowed local o text n p off t ws :
 LinkedRun.available e allowed o text ->
 (forall x,local x -> allowed x) -> valid_cursor e allowed p ->
 ip p=o+off ->
 run n (ScalarBytes.fetch o text) (State (Running off) (machine p) (carry p))=Some(t,ws) ->
 confined local ws -> let q:=finish o p (t,ws) in
 segment o text n p=Some q /\ valid_cursor e allowed q /\ StoreHistory.extends local p q.
Proof.
 intros [Image Apart] Sub [Paid W] PC Run Safe q.
 destruct (segment_history local o text n p off t ws PC (image_after _ _ _ _ _ Paid Image Apart)
   (fun x X L=>Apart x X (Sub x L)) Run Safe) as [Step Log].
 split;[exact Step|split;[split|exact Log]].
 - exact (StoreHistory.account _ _ _ _ Paid (StoreHistory.lend _ _ _ _ Sub Log)).
 - exact (segment_wf _ _ _ _ _ W Step).
Qed.
