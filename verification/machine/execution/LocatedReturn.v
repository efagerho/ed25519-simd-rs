From Coq Require Import List ZArith.
From Machine Require Import execution.Blocks execution.LinkedCalls execution.LinkedRun execution.LocatedEvents
 memory.MemoryTrace memory.FlatMemory memory.ByteExecution memory.BlockWrites memory.WriteTrace.
Local Open Scope Z_scope.

Record result:=Result { final_state:Blocks.state; resumed:cursor }.
(* Block control tracks ZF and leaves CF unspecified. The next physical
   segment can consume a carry flag only after an instruction defines it. *)
Definition execute p l loc fuel st prior:=
 match LocatedEvents.run (code_base loc) fuel p l (fst st) with
 | None=>None | Some(last,es)=>
   let d:=snd st in let ws:=LocatedEvents.stores p loc d es in
   let final:=(last,effects p (data_effects (map snd es)) d) in
   let after:=WriteTrace.replay (mem(machine prior)) ws in
   Some(Result final (Cursor (pc_word loc (rip last)) (export_state loc final after) None (log prior++ws))) end.

Theorem checked p l loc fuel tracked region st final prior after :
 (exists c es,record_path fuel p l (fst st)=Some(c,es)) -> returns p l st final ->
 byte_execution p l loc tracked region st final (mem(machine prior)) after ->
 exists ws,execute p l loc fuel st prior=Some(Result final
    (Cursor (caller_pc loc) (export_state loc final after) None (log prior++ws))) /\
 confined region ws /\ after=WriteTrace.replay (mem(machine prior)) ws.
Proof.
 intros [c [es Trace]] Ret Bytes.
 destruct(byte_execution_writes _ _ _ _ _ _ _ _ _ Bytes) as [n [events [Path [Mem Every]]]].
 rewrite (LocatedEvents.run_projection (code_base loc)) in Trace.
 destruct(LocatedEvents.run (code_base loc) fuel p l (fst st)) as [[ctrl found]|] eqn:Run;[|discriminate].
 pose proof(walk_unique _ _ _ _ _ _ Run Path) as Same;injection Same as Ctrl Ev;subst ctrl found.
 assert (Plain:record_path fuel p l (fst st)=Some(fst final,map snd events)).
 { rewrite (LocatedEvents.run_projection (code_base loc)),Run;reflexivity. }
 pose proof(proj1(record_path_sound _ _ _ _ _ _ Plain)) as PathData.
 pose proof(path_returns _ _ _ _ _ _ PathData (snd st)) as End.
 assert (F:(fst final,effects p (data_effects (map snd events)) (snd st))=final).
 { destruct st as [c0 data];exact (return_unique _ _ _ _ _ End Ret). }
 exists (LocatedEvents.stores p loc (snd st) events);split.
 - unfold execute;rewrite Run,F,(proj2 Ret),<-Mem;reflexivity.
 - split;[apply (Every events nil);symmetry;apply app_nil_r|exact Mem].
Qed.
