From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.ScalarWords
 execution.InstructionRoute execution.MappedFetch memory.WriteTrace.
From Ed25519Simd.KeyTable Require TablePackRows.
From Ed25519Simd.KeyTable Require Import CallLayout.
Import ListNotations. Local Open Scope Z_scope.

Definition choose bias:=segment (CallLayout.base bias) CallLayout.text 2.
Definition execute bias p ks:=bind (TablePackRows.run bias true p ks) (fun '(q,k)=>
 bind (choose bias q) (fun b=>TablePackRows.run bias false b k)).
Record packed (root:cpu) bias e digit p q ks:Prop:=Packed {
 address:ip q=CallLayout.base bias+1947;
 writes:accounted root (writable e) q;
 words:well_formed(machine q);
 arguments:TableMultiple.pointers e digit (machine q);
 trace:exists ws,log q=log p++ws /\ length ws=48%nat /\ confined (TablePackRows.area e digit) ws /\
    mem(machine q)=replay (mem(machine p)) ws;
 blocks:exists a b,TablePackRows.block true root bias e digit p a ks /\
    machine b=with_zf (machine a) false /\ TablePackRows.block false root bias e digit b q ks
}.

Theorem checked (root:cpu) bias e digit p ks : placement e -> loaded root bias e -> 1<=digit<=8 ->
 ip p=CallLayout.base bias+1207 -> accounted root (writable e) p -> well_formed(machine p) ->
 TableMultiple.pointers e digit (machine p) ->
 exists q,execute bias p ks=Some(q,ks) /\ packed root bias e digit p q ks.
Proof.
 intros P I N PC Acc W Ptr;set (o:=CallLayout.base bias) in *.
 destruct(TablePackRows.checked true _ _ _ _ _ ks P I N PC Acc W Ptr) as [a [First A]].
 pose proof(TablePackRows.arguments _ _ _ _ _ _ _ _ A) as PA.
 set (v:=with_zf (machine a) false).
 assert (Branch:run 2 (ScalarBytes.fetch o CallLayout.text) (State(Running 1314) (machine a) (LinkedRun.carry a))=
   Some(State(Running 1323) v (Some false),[])).
 { apply (InstructionRoute.checked _ _ _ TablePackRows.branch);cbn [TablePackRows.select follow loc cpu_state cf step option_map eval_condition with_zf flag].
   rewrite (TableMultiple.count _ _ _ PA);reflexivity. }
 pose proof(TablePackRows.writes _ _ _ _ _ _ _ _ A) as Paid;destruct(mapped_now _ _ _ I _ _ _ Paid builder_in) as [Map Sep].
 destruct(at_segment _ _ a o CallLayout.text 2 1314 _ _ Paid (TablePackRows.address _ _ _ _ _ _ _ _ A)
  Map Sep Branch (Forall_nil _)) as [Step B].
 set (b:=LinkedRun.finish o a (State(Running 1323) v (Some false),[])) in *.
 pose proof(segment_wf _ _ _ _ _ (TablePackRows.words _ _ _ _ _ _ _ _ A) Step) as BW.
 destruct(TablePackRows.checked false root bias e digit b ks P I N eq_refl B BW ltac:(destruct PA;constructor;assumption)) as [q [Rest C]].
 exists q;split;[unfold execute,choose;rewrite First;cbn [bind];fold o;rewrite Step;exact Rest|constructor].
 - exact (TablePackRows.address _ _ _ _ _ _ _ _ C).
 - exact (TablePackRows.writes _ _ _ _ _ _ _ _ C).
 - exact (TablePackRows.words _ _ _ _ _ _ _ _ C).
 - exact (TablePackRows.arguments _ _ _ _ _ _ _ _ C).
 - destruct(TablePackRows.footprint _ _ _ _ _ _ _ _ A) as [head [LA [HA [NA MA]]]].
   destruct(TablePackRows.footprint _ _ _ _ _ _ _ _ C) as [tail [LC [HC [NC MC]]]].
   exists (head++tail);split;[rewrite LC;change (log b) with (log a++[]);now rewrite app_nil_r,LA,app_assoc|].
   split;[rewrite length_app,NA,NC;reflexivity|split;[now apply Forall_app|]].
   change (mem(machine q)=replay (mem(machine p)) (head++tail));rewrite MC,replay_app;now change (mem(machine b)) with (mem(machine a));rewrite MA.
 - exists a,b;auto.
Qed.
