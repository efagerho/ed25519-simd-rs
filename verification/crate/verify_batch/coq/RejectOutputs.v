From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordBounds execution.WordSemantics
 execution.ScalarBytes execution.MappedFetch execution.LinkedRun memory.ByteMemory memory.FlatMemory
 memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.Zip215 Require ScatterBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Rows Return StageEntry Scatter.
From Ed25519Simd.VerifyBatch Require ScatterZeros.
Local Open Scope Z_scope.

Definition outputs e s := regs s 0%nat=1 /\ forall j,(j<Nat.min (count e) 8)%nat ->
 mem s (output e+Z.of_nat(position e j))=0.

(* This return begins after the wrapper's actual CALL. The return runner
   follows the metadata in that same CPU through every scatter iteration. *)
Lemma published_values mask o e p q : placement e -> (0<count e)%nat -> Scatter.indices e ->
 ip p=o -> regs(machine p) 7%nat=Rows.frame e+856 -> regs(machine p) 6%nat=output e ->
 regs(machine p) 2%nat=Z.of_nat(count e) -> regs(machine p) 0%nat=mask ->
 StageEntry.metadata e (mem(machine p)) ->
 mapped (mem(machine p)) o Zip215.ScatterBytes.symbol_bytes ->
 (forall x,o<=x<o+Z.of_nat(length Zip215.ScatterBytes.symbol_bytes) -> ~(output e<=x<output e+Z.of_nat(count e))) ->
 returning o (length Zip215.ScatterBytes.symbol_bytes) 88 p=Some q -> regs(machine q) 0%nat=1 /\
 forall j,(j<Nat.min (count e) 8)%nat ->
 mem(machine q)(output e+Z.of_nat(position e j))=ScatterValues.verdict
   (fun i=>mem(machine p)(Rows.frame e+856+Z.of_nat i)) mask j.
Proof.
 intros Place N [InRange Distinct] At DI SI DX AX [Active Indices] Map Apart Return.
 set (lanes:=Nat.min (count e) 8) in *.
 set (len:=Z.of_nat(count e)) in *;set (index:=fun j=>Z.of_nat(position e j)).
 set (meta:=Rows.frame e+856) in *.
 destruct(stack_ok _ Place) as [[S Top] _].
 assert (Idx:forall j,(j<lanes)%nat -> index_value e j=index j).
 { intros j J;unfold index_value,index,position,Policy.output_index;rewrite TailCopy.own_row by (unfold lanes in *;lia).
   symmetry;apply Z2Nat.id;apply (read_word_bound _ _ (proj2(proj2(initial_cpu _ Place)))). }
 assert (Words:ScatterValues.indices (mem(machine p)) meta lanes index).
 { intros j J;rewrite <-Idx by exact J;unfold ScatterValues.index_address,meta.
   replace (Rows.frame e+856+8) with (Rows.frame e+864) by ring;apply Indices;unfold lanes in *;lia. }
 assert (Valid:forall j,(j<lanes)%nat -> 0<=index j<len) by
    (intros j J;unfold index,len;specialize (InRange j ltac:(unfold lanes in J;lia));lia).
 assert (Len:word64 len).
 { unfold len,count;rewrite Z2Nat.id by apply (initial_cpu _ Place);apply (initial_cpu _ Place). }
 set(flags:=fun i=>mem(machine p)(meta+Z.of_nat i)).
 assert (Unique:ScatterValues.compatible index lanes (ScatterValues.verdict flags mask)).
 { intros i j I J Eq;assert (i=j) by (apply Distinct;[unfold lanes in *;lia|unfold lanes in *;lia|unfold index in Eq;lia]);now subst. }
 destruct(ScatterValues.returns mask flags o (machine p) (carry p) meta (output e) len lanes index ltac:(unfold lanes;lia)
   ltac:(unfold meta,Rows.frame,sp,fits64 in *;lia) Len (out_ok _ Place)
   ltac:(destruct(out_stack _ Place);unfold meta,Rows.frame,sp,len,disjoint in *;lia) Valid DI SI DX AX
   ltac:(unfold meta;replace (Rows.frame e+856+72) with (Rows.frame e+928) by ring;exact Active) Words ltac:(intros i K;reflexivity) Unique)
   as [t [ws [back [R [PC [Result [Zeros W]]]]]]].
 pose proof(run_lift _ _ _ _ _ _ _ R W Map Apart) as M.
 pose proof(until_exact _ _ (6+10*lanes+2)%nat 88 _ _ _ _ ltac:(unfold lanes;lia) M PC) as End.
 unfold returning in Return;rewrite At,Z.sub_diag in Return. rewrite End in Return;injection Return as <-.
 exact (conj Result Zeros).
Qed.

Lemma published o e p q : placement e -> (0<count e)%nat -> Scatter.indices e ->
 ip p=o -> regs(machine p) 7%nat=Rows.frame e+856 -> regs(machine p) 6%nat=output e ->
 regs(machine p) 2%nat=Z.of_nat(count e) -> regs(machine p) 0%nat=0 ->
 StageEntry.metadata e (mem(machine p)) ->
 mapped (mem(machine p)) o Zip215.ScatterBytes.symbol_bytes ->
 (forall x,o<=x<o+Z.of_nat(length Zip215.ScatterBytes.symbol_bytes) -> ~(output e<=x<output e+Z.of_nat(count e))) ->
 returning o (length Zip215.ScatterBytes.symbol_bytes) 88 p=Some q -> outputs e (machine q).
Proof.
 intros P N I At DI SI DX AX Meta Map Sep Run.
 destruct(published_values 0 _ _ _ _ P N I At DI SI DX AX Meta Map Sep Run) as [Status Data].
 split;[exact Status|intros j J;rewrite (Data _ J);apply ScatterZeros.rejected].
Qed.
