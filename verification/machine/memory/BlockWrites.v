From Coq Require Import List ZArith.
From Machine Require Import execution.Blocks execution.LocatedEvents memory.ByteExecution
  memory.MemoryTrace memory.FlatMemory memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

(* A returning block-kernel certificate already contains the actual ordered
   trace. Recover its instruction addresses, preserving both its flat-memory
   result and the write bound at every prefix, including inside a block. *)
Theorem locate_writes p l loc region (initial final:state) fuel events :
 record_path fuel p l (fst initial)=Some(fst final,events) ->
 (forall x,writes_at loc events x -> region x) ->
 exists located,
 LocatedEvents.run (code_base loc) fuel p l (fst initial)=Some(fst final,located) /\
 map snd located=events /\
 (forall before, WriteTrace.replay before (stores p loc (snd initial) located)=
    FlatMemory.replay p loc events (snd initial) before) /\
 forall pre tail, located=pre++tail -> confined region (stores p loc (snd initial) pre).
Proof.
 intros R Allowed. rewrite (run_projection (code_base loc)) in R.
 destruct (LocatedEvents.run _ _ _ _ _) as [[last trace]|] eqn:F;[|discriminate].
 injection R as L E. exists trace;split;[now rewrite L|split;[exact E|split]].
 - intro;rewrite replay_projection,E;reflexivity.
 - intros pre tail T. apply Forall_forall;intros w W x X.
   apply Allowed. destruct (proj1 (writes_projection p loc pre (snd initial) x)
     (ex_intro _ w (conj W X))) as [e [c [I Hit]]].
   exists e,c;split;[rewrite <-E,T,map_app;apply in_or_app;auto|exact Hit].
Qed.

Corollary byte_execution_writes p l loc tracked region initial final before after :
 byte_execution p l loc tracked region initial final before after ->
 exists fuel located,LocatedEvents.run (code_base loc) fuel p l (fst initial)=Some(fst final,located) /\
 after=WriteTrace.replay before (stores p loc (snd initial) located) /\
 forall pre tail,located=pre++tail -> confined region (stores p loc (snd initial) pre).
Proof.
 intros [_ [_ [_ [_ [fuel [es [R [M [W _]]]]]]]]].
 destruct (locate_writes _ _ _ _ _ _ _ _ R W) as [trace [T [_ [Mem Safe]]]].
 exists fuel,trace;split;[exact T|split;[rewrite Mem;exact M|exact Safe]].
Qed.
