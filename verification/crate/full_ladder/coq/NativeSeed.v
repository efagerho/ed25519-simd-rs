From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.ScalarBytes execution.ScalarWords execution.MappedFetch
 memory.FlatMemory memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.FullLadder Require Import LinkedBytes SeedPath.
From Ed25519Simd.FullLadder Require SeedProjection.
Local Open Scope Z_scope.

Definition initial v pt j:=Seed.Lane (regs v 0%nat) (vectors v j) (fun i=>SeedProjection.cell (mem v) pt i j).
Definition lane v pt base j:=Seed.execute (fun i=>SeedProjection.cell (mem v) base i j) (initial v pt j).
Definition run origin s c out ws:=MappedFetch.run (length Seed.code) (MappedFetch.fetch origin (length symbol_bytes))
    (State(Running 54) s c)=Some(State(Running 768) out c,ws).
Record result pt base s u ws:Prop:=Result {
 kept:forall g,g<>0%nat -> regs u g=regs s g;
 words:well_formed u;
 stores:confined (SeedPath.region pt) ws;
 memory:mem u=WriteTrace.replay (mem s) ws;
 rows:forall j i,(j<8)%nat -> (i<20)%nat ->
  SeedProjection.cell (mem u) pt i j=Seed.out (lane s pt base j) i
}.

Lemma valid : forallb Seed.valid Seed.code=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque Seed.code.

Theorem checked origin pt base s c : well_formed s -> regs s 3%nat=pt -> regs s 4%nat=base ->
 window pt -> window base -> disjoint pt 1280 base 1280 ->
 mapped (mem s) origin symbol_bytes ->
 (forall x,origin<=x<origin+Z.of_nat(length symbol_bytes) -> ~SeedPath.region pt x) ->
 exists u ws,run origin s c u ws /\ result pt base s u ws.
Proof.
 intros W Out Stack P B Apart Map Code.
 destruct(SeedPath.execute origin symbol_bytes pt base Seed.code 54 s c image valid P B Out Stack)
    as [u [ws [Static [G Safe]]]].
 rewrite end_offset in Static.
 pose proof(run_lift _ _ _ _ _ _ _ Static Safe Map Code) as Exec.
 exists u,ws;split;[exact Exec|constructor].
 - exact G.
 - exact (mapped_run_wf _ _ _ (State(Running 54) s c) (State(Running 768) u c) ws W Exec).
 - exact Safe.
 - exact (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Static)).
 - intros j i J I.
   pose proof(SeedProjection.execute origin symbol_bytes pt base j (fun r=>SeedProjection.cell (mem s) base r j)
      Seed.code 54 s c _ ws (initial s pt j) image valid J W Out Stack P B Apart
      ltac:(intros a A;reflexivity) ltac:(repeat split;reflexivity) Static) as [_ [_ Value]].
   unfold lane,Seed.execute. exact (Value i I).
Qed.
