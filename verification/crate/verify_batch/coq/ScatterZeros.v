From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls
 execution.ScalarBytes execution.MappedFetch execution.InstructionRoute execution.StoreInstructions
 memory.FlatMemory memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require ScatterValues.
Import ListNotations. Local Open Scope Z_scope.

Definition fetch_at:=ScatterValues.fetch_at.
Definition indices:=ScatterValues.indices.
Definition index_address:=ScatterValues.index_address.
Definition zeros m out (idx:nat->Z) n:=forall j,(j<n)%nat -> m(out+idx j)=0.

Lemma rejected flags j:ScatterValues.verdict flags 0 j=0.
Proof.
 assert (R:ScatterValues.remaining 0 j=0) by (induction j;[reflexivity|cbn [ScatterValues.remaining];now rewrite IHj]).
 unfold ScatterValues.verdict;rewrite R,Z.land_0_r;reflexivity.
Qed.

Theorem returns o s c meta out len active idx : (0<active<=8)%nat -> fits64 meta 80 ->
 word64 len -> fits64 out len -> disjoint meta 80 out len -> (forall j,(j<active)%nat -> 0<=idx j<len) ->
 regs s 7%nat=meta -> regs s 6%nat=out -> regs s 2%nat=len -> regs s 0%nat=0 ->
 read_word (mem s) (meta+72)=Z.of_nat active -> indices (mem s) meta active idx ->
 exists t ws back,run (6+10*active+2) (fetch_at o) (State (Running 0) s c)=Some(t,ws) /\
 loc t=Returned back /\ regs(cpu_state t) 0%nat=1 /\ zeros (mem(cpu_state t)) out idx active /\
 confined (fun x=>out<=x<out+len) ws.
Proof.
 intros N Meta Len Out Sep Bounds DI SI DX AX Count Ind;set(flags:=fun j=>mem s (meta+Z.of_nat j)).
 destruct(ScatterValues.returns 0 flags o s c meta out len active idx N Meta Len Out Sep Bounds DI SI DX AX Count Ind
   ltac:(intros j J;reflexivity) ltac:(intros i j I J E;now rewrite !rejected)) as [t [ws [back [Run [PC [Status [Data Safe]]]]]]].
 exists t,ws,back;split;[exact Run|split;[exact PC|split;[exact Status|split;[|exact Safe]]]].
 intros j J;rewrite (Data _ J);apply rejected.
Qed.
