From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.MappedFetch execution.InstructionRoute memory.ByteMemory memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Image Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require RejectExecution Scattered ScoreTail.
Import ListNotations. Local Open Scope Z_scope.

Definition jump:list line:=[(539,2%nat,ScalarBytes.Jump (574-541))].
Lemma image pc dst text : matches pc dst text -> linked text jump.
Proof. intros [<- Fits];constructor;[split;[lia|reflexivity]|constructor]. Qed.
Definition execute origin text p:=bind (segment origin text 1 p) (fun cont=>
 option_map (RejectExecution.classify cont) (RejectFinish.leave origin text cont)).

Theorem checked_with (values:FlatMemory.bytes->Prop) bias pc dst text e p :
 matches pc dst text -> RejectFinish.bound text -> placement e ->
 mapped (mem e) (bias+pc) text -> (forall x,bias+pc<=x<bias+pc+Z.of_nat(length text) -> ~writable e x) ->
 ip p=bias+pc+539 -> regs(machine p) 4%nat=Rows.frame e -> accounted e (writable e) p ->
 regs(machine p) 12%nat=Prologue.rows_left (regs e 6%nat) -> StageEntry.saved_caller e (machine p) ->
 (regs(machine p) 0%nat=1 /\ values(mem(machine p))) -> byte_memory(mem(machine p)) ->
 exists r,execute (bias+pc) text p=Some r /\ RejectExecution.post_with values (bias+pc) e r.
Proof.
 intros Image Exit P Map Sep At Stack Paid Left Saved Output Bytes.
 set (o:=bias+pc) in *.
 assert (Step:run 1 (ScalarBytes.fetch o text) (State(Running 539)(machine p)(carry p))=
   Some(State(Running 574)(machine p)(carry p),[])).
 { apply (InstructionRoute.checked _ _ _ (image _ _ _ Image));reflexivity. }
 destruct(at_segment _ _ p o text 1 539 _ _ Paid At (image_after _ _ _ _ _ Paid Map Sep) Sep Step (Forall_nil _)) as [Jump Acc].
 set (cont:=LinkedRun.finish o p (State(Running 574)(machine p)(carry p),[])) in *.
 assert (Continued:RejectDispatch.continued bias pc e cont) by (exact (conj eq_refl (conj Stack (conj Acc Left)))).
 destruct(RejectFinish.next _ _ _ _ _ Exit P Map Sep Continued Saved) as [q [Done Post]].
 exists(RejectExecution.classify cont q);split;[unfold execute;rewrite Jump;change (option_map (RejectExecution.classify cont) (RejectFinish.leave (bias+pc) text cont)=Some(RejectExecution.classify cont q));now rewrite Done|].
 exact (RejectExecution.classified_with values o e cont q P Left Post Output Bytes).
Qed.

Theorem checked bias pc dst text e p :
 matches pc dst text -> RejectFinish.bound text -> placement e ->
 mapped (mem e) (bias+pc) text -> (forall x,bias+pc<=x<bias+pc+Z.of_nat(length text) -> ~writable e x) ->
 ip p=bias+pc+539 -> regs(machine p) 4%nat=Rows.frame e -> accounted e (writable e) p ->
 regs(machine p) 12%nat=Prologue.rows_left (regs e 6%nat) -> StageEntry.saved_caller e (machine p) ->
 RejectOutputs.outputs e (machine p) -> byte_memory(mem(machine p)) ->
 exists r,execute (bias+pc) text p=Some r /\ RejectExecution.post (bias+pc) e r.
Proof. exact (checked_with (RejectExecution.zero_results e) bias pc dst text e p). Qed.
